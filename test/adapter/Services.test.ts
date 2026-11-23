import { expect, test } from "bun:test";
import {
  Brand,
  Clock,
  Duration,
  Effect,
  Equal,
  Fiber,
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
const twoTo32 = 2 ** 32;

/** Starts the program, runs every queued task; answers what it kept. */
const runToEnd = <A>(
  program: Effect.Effect<A, unknown, Durable>,
  draws: number[] = [],
) => {
  const log = asked();
  const kept: A[] = [];
  const keep = (value: A) => Effect.sync(() => {
    kept.push(value);
  });
  const adapter = makeAdapter(
    Effect.tap(program, keep),
    0,
    askingHost(log, draws),
  );
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

test("Clock.currentTimeMillis returns the host's answer", () => {
  const { log, kept } = runToEnd(Effect.all([
    Clock.currentTimeMillis,
    unsafeMillis,
  ]));
  expect(kept).toEqual([[1_000, 1_000]]);
  expect(log.clock).toEqual([fiberId(0), fiberId(0)]);
});

test("the nanosecond readers answer the host's millis times 10^6", () => {
  const { kept } = runToEnd(Effect.all([
    Clock.currentTimeNanos,
    Clock.monotonicTimeNanos,
  ]));
  expect(kept).toEqual([[1_000_000_000n, 1_000_000_000n]]);
});

test("two draws from two fibers ask with each fiber's id", () => {
  const { log, kept } = runToEnd(
    Effect.all([Random.next, Random.next], { concurrency: "unbounded" }),
    [twoTo32 / 4, twoTo32 / 2],
  );
  expect(log.draw).toEqual([fiberId(1), fiberId(2)]);
  expect(kept).toEqual([[0.25, 0.5]]);
});

test("nextInt takes a sign and 53 bits from two draws", () => {
  const top = 2 ** 21;
  const { kept } = runToEnd(Effect.all([Random.nextInt, Random.nextInt]), [
    top - 1,
    twoTo32 - 1,
    top + 1,
    2,
  ]);
  expect(kept).toEqual([[Number.MAX_SAFE_INTEGER, -(twoTo32 + 2)]]);
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
  const inputs: Duration.Input[] = [
    "1500 micros",
    0,
    "Infinity",
    "-0.5 millis",
    "-3 millis",
    "-Infinity",
  ];
  expect(inputs.map(sleepSent)).toEqual([
    [millis(2)],
    [millis(0)],
    [forever],
    [millis(0)],
    [millis(-3)],
    [millis(0)],
  ]);
});

/** Runs a sleep of 5 ms then 7, answers it, and gives the root's exit. */
const answeredSleep = (outcome: Outcome) => {
  const { log, runTask } = runToEnd(Effect.as(Effect.sleep(5), 7));
  runTask({ _tag: "Deliver", fiber: fiberId(0), token: token(0), outcome });
  return log.events.at(-1);
};

test("a sleep resumes on a Value and dies on a Failure", () => {
  expect(answeredSleep({ _tag: "Value", value: 0 })).toEqual({
    _tag: "RootExit",
    exit: { _tag: "Success", value: 7 },
  });
  expect(answeredSleep({ _tag: "Failure", value: 2 })).toEqual({
    _tag: "RootExit",
    exit: { _tag: "Defect" },
  });
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
  const defect: Event = { _tag: "RootExit", exit: { _tag: "Defect" } };
  for (const read of [Clock.currentTimeMillis, unsafeMillis, Random.next]) {
    const log = unregistered<unknown>(read);
    expect(log.events.at(-1)).toEqual(defect);
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
  expect(log.noted).toEqual([
    "Date.now",
    "Math.random",
    "setTimeout",
    "setImmediate",
    "Date.now",
  ]);
});

test("withGlobalSourceLog restores the globals, even after a throw", () => {
  const log = asked();
  const host = askingHost(log, []);
  withGlobalSourceLog(host, () => 0);
  const fails = () => {
    throw new Error("inside");
  };
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
  expect(log.events.at(-1)).toEqual({
    _tag: "RootExit",
    exit: { _tag: "Success", value: 0 },
  });
});
