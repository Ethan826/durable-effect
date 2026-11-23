import {
  Clock,
  DateTime,
  Deferred,
  Duration,
  Effect,
  Fiber,
  Logger,
  Option,
  Queue,
  Random,
  Ref,
  Schedule,
} from "effect";
import { durable } from "../src/adapter/Durable.ts";
import type { Durable } from "../src/adapter/Durable.ts";
import type { Op } from "../src/adapter/Interface.ts";
import type { Program, Sequence, Statement, Tag } from "./grammar.ts";

/** What every statement of one program run shares. */
interface Shared {
  readonly program: Program;
  readonly refs: readonly [Ref.Ref<number>, Ref.Ref<number>];
  readonly deferreds: readonly [
    Deferred.Deferred<void>,
    Deferred.Deferred<void>,
  ];
  readonly queue: Queue.Queue<number>;
  /** The fiber forked from each fork body, by its index. */
  readonly handles: Map<number, Fiber.Fiber<unknown, unknown>>;
}

type Step = Effect.Effect<unknown, unknown, Durable>;
type Interpreters = {
  readonly [K in Tag]: (statement: Statement<K>, shared: Shared) => Step;
};

/** A call to another handler: a `Run` of a kind no `run` step uses. */
const callKind = 3;
const failValue = 1;
const spacing = Duration.millis(1);

const runOp = (kind: number): Op => ({ _tag: "Run", kind, args: 0 });

/** `count` pure steps, each one Effect operation. */
const loop = (count: number): Effect.Effect<void> =>
  Effect.suspend(() => {
    let done = 0;
    return Effect.whileLoop({
      while: () => done < count,
      body: () => Effect.sync(() => done++),
      step: () => {},
    });
  });

type Retried = (attempt: Effect.Effect<void, number>) => Step;

/**
 * Retries an attempt that fails on its first `times - 1` tries and
 * succeeds on the last. The count lives outside the retried effect, which
 * `retry` runs afresh on every try.
 */
const retryUntil = (times: number, retried: Retried): Step =>
  Effect.suspend(() => {
    let tries = 0;
    return retried(Effect.suspend(() => {
      tries += 1;
      return tries < times ? Effect.fail(failValue) : Effect.void;
    }));
  });

const spacedSchedule = (jittered: boolean) =>
  jittered ? Schedule.jittered(Schedule.spaced(spacing)) :
    Schedule.spaced(spacing);

const spanned = Effect.fn("conformance.span")(function* (count: number) {
  yield* loop(count);
});

const caughtOr = <E>(caught: boolean, effect: Effect.Effect<never, E>) =>
  caught ? Effect.catchCause(effect, () => Effect.void) : effect;

/** Two fibers, each awaiting a deferred that the other completes. */
const deadlock = Effect.all([Deferred.make<void>(), Deferred.make<void>()])
  .pipe(Effect.flatMap(([first, second]) =>
    Effect.forkChild(Effect.andThen(
      Deferred.await(first),
      Deferred.succeed(second, undefined),
    )).pipe(
      Effect.andThen(Deferred.await(second)),
      Effect.andThen(Deferred.succeed(first, undefined)),
    )
  ));

/** Forks body `fiber` unless it was forked already: one fiber per body. */
const forkBody = (
  statement: Statement<"Fork">,
  shared: Shared,
): Step => Effect.suspend(() => {
  if (shared.handles.has(statement.fiber)) return Effect.void;
  const body = sequence(shared.program.forks[statement.fiber] ?? [], shared);
  const forked = statement.detach
    ? Effect.forkDetach(body)
    : Effect.forkChild(body);
  return Effect.map(forked, (fiber) => {
    shared.handles.set(statement.fiber, fiber);
  });
});

/** Acts on the fiber forked from body `fiber`; nothing if there is none. */
const onHandle = (act: (fiber: Fiber.Fiber<unknown, unknown>) => Step) =>
  (statement: { readonly fiber: number }, shared: Shared): Step =>
    Effect.suspend(() => {
      const fiber = shared.handles.get(statement.fiber);
      return Option.match(Option.fromUndefinedOr(fiber), {
        onNone: () => Effect.void,
        onSome: act,
      });
    });

const pollOnce = (fiber: Fiber.Fiber<unknown, unknown>) =>
  Effect.sync(() => fiber.pollUnsafe());

/** A finalizer must not fail; its failures are dropped, defects kept. */
const finalizer = (statements: Sequence, shared: Shared) =>
  Effect.ignore(sequence(statements, shared));

type Some = Partial<Interpreters>;

/** Durable steps, time, randomness, loops and failures. */
const basicSteps = {
  Run: ({ kind }) => durable(runOp(kind)),
  Sleep: ({ millis }) => Effect.sleep(Duration.millis(millis)),
  ClockRead: () => Clock.currentTimeMillis,
  RandomDraw: () => Random.next,
  YieldNow: () => Effect.yieldNow,
  Loop: ({ count }) => loop(count),
  Repeat: ({ count }) => Effect.repeat(loop(1), Schedule.recurs(count - 1)),
  Retry: ({ count }) => retryUntil(count, (attempt) =>
    Effect.retry(attempt, Schedule.recurs(count - 1))),
  Timeout: ({ count, millis }) =>
    Effect.timeout(loop(count), Duration.millis(millis)),
  RacePure: ({ left, right }) => Effect.race(loop(left), loop(right)),
  RaceDurable: ({ count, kind }) =>
    Effect.race(durable(runOp(kind)), loop(count)),
  Fail: ({ caught }) => caughtOr(caught, Effect.fail(failValue)),
  Die: ({ caught }) => caughtOr(caught, Effect.die("scripted defect")),
} satisfies Some;

/** Spaced schedules, telemetry, calls and the statements that block. */
const scheduledSteps = {
  RetrySpaced: ({ steps, jittered }) => retryUntil(steps, (attempt) =>
    Effect.retry(attempt, {
      schedule: spacedSchedule(jittered),
      times: steps - 1,
    })),
  RepeatSpaced: ({ steps, jittered }) => Effect.repeat(loop(1), {
    schedule: spacedSchedule(jittered),
    times: steps - 1,
  }),
  Timed: ({ count }) => Effect.timed(loop(count)),
  DateTimeNow: () => DateTime.now,
  Log: () => Effect.log("conformance statement"),
  FnSpan: ({ count }) => spanned(count),
  Call: () => durable(runOp(callKind)),
  Never: () => Effect.never,
  Deadlock: () => deadlock,
} satisfies Some;

/** Immediate forks, caching, and the shared refs, deferreds and queue. */
const sharedSteps = {
  All: ({ counts, durable: withDurable, concurrency }) => Effect.all(
    [...counts.map(loop), ...(withDurable ? [durable(runOp(0))] : [])],
    { concurrency, discard: true },
  ),
  ForEach: ({ counts }) =>
    Effect.forEach(counts, loop, { concurrency: "unbounded", discard: true }),
  Cached: ({ count }) =>
    Effect.flatMap(Effect.cached(loop(count)), (once) =>
      Effect.andThen(once, once)),
  RefUpdate: ({ ref }, shared) =>
    Ref.update(shared.refs[ref], (value) => value + 1),
  RefGet: ({ ref }, shared) => Ref.get(shared.refs[ref]),
  DeferredSucceed: ({ deferred }, shared) =>
    Deferred.succeed(shared.deferreds[deferred], undefined),
  DeferredAwait: ({ deferred }, shared) =>
    Deferred.await(shared.deferreds[deferred]),
  QueueOffer: (_, shared) => Queue.offer(shared.queue, 1),
  QueueTake: (_, shared) => Queue.take(shared.queue),
} satisfies Some;

/** Forked fibers, and the statements that hold sub-sequences. */
const structuredSteps = {
  Fork: forkBody,
  Join: onHandle(Fiber.join),
  Interrupt: onHandle(Fiber.interrupt),
  Poll: onHandle(pollOnce),
  Uninterruptible: ({ body }, shared) =>
    Effect.uninterruptible(sequence(body, shared)),
  Ensuring: ({ body, finalizer: last }, shared) =>
    Effect.ensuring(sequence(body, shared), finalizer(last, shared)),
  AcquireRelease: ({ acquire, release }, shared) =>
    Effect.scoped(Effect.acquireRelease(
      sequence(acquire, shared),
      () => finalizer(release, shared),
    )),
} satisfies Some;

const interpreters: Interpreters = {
  ...basicSteps,
  ...scheduledSteps,
  ...sharedSteps,
  ...structuredSteps,
};

const interpretOne = <K extends Tag>(statement: Statement<K>, shared: Shared) =>
  interpreters[statement._tag](statement, shared);

/** The statements in order; the sequence ends at the first failure. */
const sequence = (statements: Sequence, shared: Shared): Step =>
  Effect.forEach(statements, (one) => interpretOne(one, shared), {
    discard: true,
  });

/** Log lines go nowhere, so a run prints nothing. */
const silentLoggers = new Set([Logger.make(() => undefined)]);

const makeShared = Effect.all({
  refs: Effect.all([Ref.make(0), Ref.make(0)]),
  deferreds: Effect.all([Deferred.make<void>(), Deferred.make<void>()]),
  queue: Queue.unbounded<number>(),
});

/**
 * The Effect a program stands for: fresh shared refs, deferreds and queue,
 * then the root body. Each fork body runs when a `Fork` names it, at most
 * once per run. Log output is discarded.
 */
export const interpret = (
  program: Program,
): Effect.Effect<void, unknown, Durable> =>
  makeShared.pipe(
    Effect.flatMap((made) =>
      sequence(program.root, { ...made, program, handles: new Map() })
    ),
    Effect.asVoid,
    Effect.provideService(Logger.CurrentLoggers, silentLoggers),
  );
