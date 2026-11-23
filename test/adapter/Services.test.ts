import { expect, test } from "bun:test";
import {
  Brand,
  Clock,
  Duration,
  Effect,
  Equal,
  Fiber,
  Logger,
  Random,
  Scheduler,
} from "effect";
import type { Durable } from "../../src/adapter/Durable.ts";
import type {
  Event,
  FiberId,
  GlobalSource,
  Host,
  Op,
  Outcome,
  RootExit,
  Token,
} from "../../src/adapter/Interface.ts";
import { makeAdapter } from "../../src/adapter/Runtime.ts";
import { withGlobalSourceLog } from "../../src/adapter/Services.ts";

/** Every question the host was asked, in order, by kind. */
interface Asked {
  readonly events: Event[];
  readonly clock: FiberId[];
  readonly draw: FiberId[];
  readonly noted: GlobalSource[];
}

const asked = (): Asked => ({ events: [], clock: [], draw: [], noted: [] });

/** A host that logs every question; the clock answers 1000 plus the id. */
const askingHost = (log: Asked, draws: number[]): Host => ({
  emit: (event) => {
    log.events.push(event);
  },
  clock: (fiber) => {
    log.clock.push(fiber);
    return 1_000 + fiber;
  },
  draw: (fiber) => {
    log.draw.push(fiber);
    return draws.shift() ?? 0;
  },
  register: () => false,
  inSlice: () => true,
  foreign: () => {},
  noteGlobal: (source) => {
    log.noted.push(source);
  },
});

const fiberId = Brand.nominal<FiberId>();
const token = Brand.nominal<Token>();
const rootExit = (exit: RootExit): Event => ({ _tag: "RootExit", exit });

const keepIn = <A>(kept: A[]) => (value: A) => Effect.sync(() => {
  kept.push(value);
});

/** Starts the program, runs every queued task; answers what it kept. */
const runToEnd = <A>(
  program: Effect.Effect<A, unknown, Durable>,
  draws: number[] = [],
) => {
  const log = asked();
  const kept: A[] = [];
  const host = askingHost(log, draws);
  const adapter = makeAdapter(Effect.tap(program, keepIn(kept)), 0, host);
  adapter.runTask({ _tag: "StartRoot" });
  let seen = 0;
  while (seen < log.events.length) {
    const entry = log.events[seen++];
    if (entry?._tag === "Queue") {
      adapter.runTask({ _tag: "RunQueued", task: entry.task });
    }
  }
  return { log, kept, runTask: adapter.runTask };
};

const unsafeMillis = Clock.clockWith((clock) =>
  Effect.sync(() => clock.currentTimeMillisUnsafe())
);

test("every clock reader answers the host's millis, nanos times 10^6", () => {
  const { log, kept } = runToEnd(Effect.all([
    Clock.currentTimeMillis,
    unsafeMillis,
    Clock.currentTimeNanos,
    Clock.monotonicTimeNanos,
  ]));
  expect(kept).toEqual([[1_000, 1_000, 1_000_000_000n, 1_000_000_000n]]);
  expect(log.clock).toEqual([0, 0, 0, 0].map(fiberId));
});

/** A logger that keeps the timestamp of each line. */
const stampLogger = (stamps: number[]) =>
  Logger.make(({ date }) => {
    stamps.push(date.getTime());
  });

/** Two log lines inside a span; answers the span's start time. */
const loggedSpan = Effect.withSpan(
  Effect.andThen(
    Effect.andThen(Effect.log("first"), Effect.log("second")),
    Effect.map(Effect.currentSpan, (span) => span.status.startTime),
  ),
  "work",
);

// Revision 5's time rule: a clock read is not journaled, and with no
// durable await between them two reads ask at the same point in L.
test("Effect's log and span stamps ask host.clock for the root", () => {
  const stamps: number[] = [];
  const { log, kept } = runToEnd(Effect.provideService(
    loggedSpan,
    Logger.CurrentLoggers,
    new Set([stampLogger(stamps)]),
  ));
  expect(stamps).toEqual([1_000, 1_000]);
  expect(kept).toEqual([1_000_000_000n]);
  expect(log.clock.length).toBeGreaterThanOrEqual(3);
  expect(new Set(log.clock)).toEqual(new Set([fiberId(0)]));
});

const millis = (amount: number): Op => ({
  _tag: "Sleep",
  duration: { _tag: "Millis", millis: amount },
});
const forever: Op = { _tag: "Sleep", duration: { _tag: "Forever" } };

/** The op of the one Start a sleep of this duration reports. */
const sleepSent = (duration: Duration.Input) =>
  runToEnd(Effect.sleep(duration)).log.events.flatMap((event) =>
    event._tag === "Start" ? [event.op] : []
  );

// Rounding -0.5 up gives -0, which a journal would print as 0 but toEqual
// tells apart; -Infinity has no whole number of milliseconds.
test("Clock.sleep is a durable sleep of whole milliseconds, rounded up", () => {
  const table: Array<readonly [Duration.Input, Op]> = [
    ["1500 micros", millis(2)],
    [0, millis(0)],
    ["Infinity", forever],
    ["-0.5 millis", millis(0)],
    ["-3 millis", millis(-3)],
    ["-Infinity", millis(0)],
    [Duration.millis(Number.MAX_SAFE_INTEGER + 2), forever],
  ];
  for (const [input, op] of table) expect(sleepSent(input)).toEqual([op]);
});

/** Runs a sleep of 5 ms then 7, answers it, and gives the root's exit. */
const answeredSleep = (outcome: Outcome) => {
  const { log, runTask } = runToEnd(Effect.as(Effect.sleep(5), 7));
  runTask({ _tag: "Deliver", fiber: fiberId(0), token: token(0), outcome });
  return log.events.at(-1);
};

test("a sleep resumes on a Value and dies on a Failure", () => {
  expect(answeredSleep({ _tag: "Value", value: 0 }))
    .toEqual(rootExit({ _tag: "Success", value: 7 }));
  expect(answeredSleep({ _tag: "Failure", value: 2 }))
    .toEqual(rootExit({ _tag: "Defect" }));
});

// PreventSchedulerYield keeps the child from ever reaching shouldYield, so
// it has no id to ask the host with; the read dies, as an await does.
const unregistered = <A>(read: Effect.Effect<A>) =>
  runToEnd(Effect.provideService(
    Effect.flatMap(Effect.forkChild(read), Fiber.join),
    Scheduler.PreventSchedulerYield,
    true,
  )).log;

test("a clock or random read on an unregistered fiber dies", () => {
  for (const read of [Clock.currentTimeMillis, unsafeMillis, Random.next]) {
    const log = unregistered<unknown>(read);
    expect(log.events.at(-1)).toEqual(rootExit({ _tag: "Defect" }));
    expect([...log.clock, ...log.draw]).toEqual([]);
  }
});

/** Calls each of the four globals once. */
const useGlobals = () => {
  Date.now();
  Math.random();
  clearTimeout(setTimeout(() => {}, 0));
  clearImmediate(setImmediate(() => {}));
};

test("withGlobalSourceLog notes each global, then calls the original", () => {
  const log = asked();
  const before = Date.now();
  const now = withGlobalSourceLog(askingHost(log, []), () => {
    useGlobals();
    return Date.now();
  });
  expect(now).toBeGreaterThanOrEqual(before);
  const sources = ["Date.now", "Math.random", "setTimeout", "setImmediate"];
  expect<string[]>(log.noted).toEqual([...sources, "Date.now"]);
});

test("withGlobalSourceLog restores the globals, even after a throw", () => {
  const log = asked();
  const host = askingHost(log, []);
  withGlobalSourceLog(host, () => 0);
  const fails = () => { throw new Error("inside"); };
  expect(() => withGlobalSourceLog(host, fails)).toThrow("inside");
  useGlobals();
  expect(log.noted).toEqual([]);
});

// Review Focus 5: Effect hashes a function with Hash.random, which calls
// Math.random; a structural Equal.equals over fresh functions reaches it.
const equalsOverFunctions = Effect.sync(() => {
  const first = () => 1;
  const second = () => 2;
  return Equal.equals({ run: first }, { run: second });
});

test("Effect's own Math.random during a task is noted, not fatal", () => {
  const { log, kept } = runToEnd(equalsOverFunctions);
  expect(kept).toEqual([false]);
  expect(log.noted).toContain("Math.random");
  expect(log.events.at(-1)).toEqual(rootExit({ _tag: "Success", value: 0 }));
});
