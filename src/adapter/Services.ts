import {
  Clock,
  Context,
  Duration,
  Effect,
  Fiber,
  Option,
  Random,
} from "effect";
import { UnregisteredFiber } from "./Durable.ts";
import type { FiberId, GlobalSource, Host, Op } from "./Interface.ts";
import type { AdapterState } from "./State.ts";

/** Starts a durable operation and awaits its outcome (`Durable.await`). */
type AwaitOp = (op: Op) => Effect.Effect<number, number>;

const nanosPerMilli = BigInt(1_000_000);
const twoTo32 = 2 ** 32;
const twoTo21 = 2 ** 21;

/** The id the adapter gave this fiber, if it has registered it. */
const idOf = (state: AdapterState) =>
  (fiber: Fiber.Fiber<unknown, unknown> | undefined): Option.Option<FiberId> =>
    Option.fromUndefinedOr(fiber).pipe(
      Option.flatMap((seen) => Option.fromUndefinedOr(state.fibers.get(seen))),
      Option.map((known) => known.id),
    );

/**
 * The defect of a read on a fiber the adapter never registered. Effect
 * calls a service's unsafe readers synchronously inside a fiber's step, so
 * a throw is the only way out of one. The run loop catches it and the fiber
 * dies with it (effect 4.1.5 internal/effect.ts:727-731), as an await on
 * such a fiber does.
 */
const unregistered = (): never => {
  throw new UnregisteredFiber();
};

/** The current fiber's id, for the synchronous readers. */
const currentIdUnsafe = (state: AdapterState): FiberId =>
  Option.getOrElse(idOf(state)(Fiber.getCurrent()), unregistered);

/** An effect that asks the host about the current fiber when it runs. */
const askEffect = (state: AdapterState, ask: (fiber: FiberId) => number) =>
  Effect.withFiber((fiber) =>
    Option.match(idOf(state)(fiber), {
      onNone: () => Effect.die(new UnregisteredFiber()),
      onSome: (id) => Effect.succeed(ask(id)),
    })
  );

const toNanos = (millis: number): bigint => BigInt(millis) * nanosPerMilli;

/**
 * Whole milliseconds, rounded up. Negative infinity becomes 0, which the
 * executor treats as a yield, as it does any sleep of 0 ms or less. Adding
 * 0 turns the -0 that rounding a small negative gives into 0.
 */
const wholeMillis = (millis: number): number =>
  millis === -Infinity ? 0 : Math.ceil(millis) + 0;

/**
 * The durable sleep for a duration. An infinite one sleeps forever, and so
 * does one longer than `Number.MAX_SAFE_INTEGER` whole milliseconds: that
 * has no exact integer, and such a sleep could never end in practice.
 */
const sleepOp = (duration: Duration.Duration): Op => {
  const millis = wholeMillis(Duration.toMillis(duration));
  if (millis > Number.MAX_SAFE_INTEGER) {
    return { _tag: "Sleep", duration: { _tag: "Forever" } };
  }
  return { _tag: "Sleep", duration: { _tag: "Millis", millis } };
};

/** A durable sleep; a `Failure` outcome, which no sleep should get, dies. */
const durableSleep = (awaitOp: AwaitOp) =>
  (duration: Duration.Duration): Effect.Effect<void> =>
    Effect.orDie(Effect.asVoid(awaitOp(sleepOp(duration))));

/**
 * The adapter's `Clock`, by design revision 5's time rule. Every reader
 * asks `host.clock` with the current fiber's id: the millisecond readers
 * answer it as is, and the wall and monotonic nanosecond readers answer it
 * times 10^6. `sleep` is a durable `Sleep` of the duration in whole
 * milliseconds, rounded up, through the `Durable` service's await.
 * Effect's own log, span and error-report timestamps read this clock too.
 * Such a read is not journaled (design revision 5, the time rule); stamps
 * in real time belong to the telemetry layer.
 */
export const makeClock = (
  state: AdapterState,
  host: Host,
  awaitOp: AwaitOp,
): Clock.Clock => {
  const millisUnsafe = () => host.clock(currentIdUnsafe(state));
  const nanosUnsafe = () => toNanos(millisUnsafe());
  const millis = askEffect(state, host.clock);
  const nanos = Effect.map(millis, toNanos);
  return {
    currentTimeMillisUnsafe: millisUnsafe,
    currentTimeMillis: millis,
    currentTimeNanosUnsafe: nanosUnsafe,
    currentTimeNanos: nanos,
    monotonicTimeNanosUnsafe: nanosUnsafe,
    monotonicTimeNanos: nanos,
    sleep: durableSleep(awaitOp),
  };
};

/**
 * A safe integer from two draws, the first taken first. The low 21 bits of
 * the first and all 32 of the second give a magnitude in [0, 2^53 - 1]; bit
 * 21 of the first gives the sign. Zero has both signs, so it comes up twice
 * as often as any other value.
 */
const safeInteger = (high: number, low: number): number => {
  const magnitude = (high % twoTo21) * twoTo32 + low;
  const negative = Math.floor(high / twoTo21) % 2 === 1;
  return negative ? 0 - magnitude : magnitude;
};

/**
 * The adapter's `Random`, built from `host.draw`, which answers a 32-bit
 * unsigned integer for the current fiber. Effect 4.1.5's `Random` has two
 * methods, and every generator in `effect/Random` and `Schedule` goes
 * through them: `nextDoubleUnsafe` is one draw divided by 2^32, in [0, 1);
 * `nextIntUnsafe` is two draws read as a sign and 53 bits.
 */
export const makeRandom = (
  state: AdapterState,
  host: Host,
): Random.Random => {
  const draw = () => host.draw(currentIdUnsafe(state));
  return {
    nextDoubleUnsafe: () => draw() / twoTo32,
    nextIntUnsafe: () => safeInteger(draw(), draw()),
  };
};

/**
 * The context that replaces Effect's `Clock` and `Random` references with
 * the adapter's, for one adapter's state and host. It is a context, not a
 * merged layer, because `Layer.mergeAll` builds its layers in forked fibers,
 * and each would take a fiber id ahead of the program's own.
 */
export const deterministicServices = (
  state: AdapterState,
  host: Host,
  awaitOp: AwaitOp,
): Context.Context<never> => Context.make(
  Clock.Clock,
  makeClock(state, host, awaitOp),
).pipe(Context.add(Random.Random, makeRandom(state, host)));

type LoggedGlobal = readonly [object, string, GlobalSource];

const loggedGlobals: ReadonlyArray<LoggedGlobal> = [
  [Date, "now", "Date.now"],
  [Math, "random", "Math.random"],
  [globalThis, "setTimeout", "setTimeout"],
  [globalThis, "setImmediate", "setImmediate"],
];

/**
 * Replaces one global with a version that notes each use and then calls
 * the original; answers the step that puts the original back. A runtime
 * without the global is left alone.
 */
const replaceGlobal = (host: Host) => (logged: LoggedGlobal) => {
  const [target, key, source] = logged;
  const original: unknown = Reflect.get(target, key);
  if (typeof original !== "function") return () => {};
  const noted = (...args: unknown[]): unknown => {
    host.noteGlobal(source);
    return Reflect.apply(original, target, args);
  };
  Reflect.set(target, key, noted);
  return () => {
    Reflect.set(target, key, original);
  };
};

const restore = (step: () => void) => step();

/**
 * Runs `f` with `Date.now`, `Math.random`, `setTimeout` and `setImmediate`
 * replaced by versions that report each use through `host.noteGlobal` and
 * then call the original, so a use is seen but its result is unchanged
 * (report-only, #37 I2). The originals are back when `f` returns or throws.
 * The log does not see a reference taken before the task (for example
 * `const now = Date.now`), `new Date()`, `performance.now`, `setInterval`
 * or `queueMicrotask`.
 */
export const withGlobalSourceLog = <A>(host: Host, f: () => A): A => {
  const restores = loggedGlobals.map(replaceGlobal(host));
  try {
    return f();
  } finally {
    restores.forEach(restore);
  }
};
