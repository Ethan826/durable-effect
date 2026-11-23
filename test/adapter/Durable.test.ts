import { expect, test } from "bun:test";
import { Brand, Effect, Fiber, Scheduler } from "effect";
import {
  deliver as answer,
  durable,
  Durable,
  makeDurable,
} from "../../src/adapter/Durable.ts";
import { registration, requestInterrupt } from "../../src/adapter/Fibers.ts";
import type {
  Event,
  FiberId,
  Host,
  Op,
  Outcome,
  RootExit,
  Task,
  Token,
} from "../../src/adapter/Interface.ts";
import { makeAdapter } from "../../src/adapter/Runtime.ts";
import { deterministicScheduler } from "../../src/adapter/Scheduler.ts";
import { makeState } from "../../src/adapter/State.ts";

/** A host that logs every event; registration never asks to interrupt. */
const loggingHost = (log: Event[]): Host => ({
  emit: (event) => {
    log.push(event);
  },
  clock: () => 0,
  draw: () => 0,
  register: () => false,
  inSlice: () => true,
  foreign: () => {},
});

const fiberId = Brand.nominal<FiberId>();
const token = Brand.nominal<Token>();
const run: Op = { _tag: "Run", kind: 1, args: 2 };
const sleep: Op = { _tag: "Sleep", duration: { _tag: "Millis", millis: 5 } };
const value = (amount: number): Outcome => ({ _tag: "Value", value: amount });

const start = (fiber: number, tok: number, op: Op): Event => ({
  _tag: "Start",
  fiber: fiberId(fiber),
  token: token(tok),
  op,
});
const release = (fiber: number, tok: number): Event => ({
  _tag: "Release",
  fiber: fiberId(fiber),
  token: token(tok),
});
const deliveredTo = (fiber: number, tok: number) => ({
  fiber: fiberId(fiber),
  token: token(tok),
  outcome: value(1),
});
const deliver = (fiber: number, tok: number, outcome: Outcome): Task => ({
  _tag: "Deliver",
  fiber: fiberId(fiber),
  token: token(tok),
  outcome,
});
const cancel = (fiber: number, tok: number): Task => ({
  _tag: "DeliverCancel",
  fiber: fiberId(fiber),
  token: token(tok),
});
const interruptRoot: Task = { _tag: "RequestInterrupt", fiber: fiberId(0) };

/** Starts a program on a fresh adapter; answers its task runner. */
const started = (program: Effect.Effect<unknown, unknown, Durable>) => {
  const log: Event[] = [];
  const adapter = makeAdapter(program, 0, loggingHost(log));
  adapter.runTask({ _tag: "StartRoot" });
  return { log, runTask: adapter.runTask };
};

/** Sends `RunQueued` for every `Queue` in the log, oldest first. */
const drain = (runTask: (task: Task) => void, log: Event[]) => {
  let seen = 0;
  while (seen < log.length) {
    const entry = log[seen++];
    if (entry?._tag === "Queue") {
      runTask({ _tag: "RunQueued", task: entry.task });
    }
  }
};

const exitWith = (exit: RootExit): Event => ({ _tag: "RootExit", exit });
const rootEnd = (exit: RootExit): Event[] => [
  { _tag: "FiberExited", fiber: fiberId(0) },
  exitWith(exit),
];

test("a durable await starts, then a Deliver resumes with its value", () => {
  const { log, runTask } = started(durable(run));
  expect(log).toEqual([start(0, 0, run)]);
  runTask(deliver(0, 0, value(5)));
  expect(log.slice(1)).toEqual(rootEnd({ _tag: "Success", value: 5 }));
});

test("a Failure outcome fails the fiber with its value", () => {
  const { log, runTask } = started(durable(run));
  runTask(deliver(0, 0, { _tag: "Failure", value: 3 }));
  expect(log.at(-1)).toEqual(exitWith({ _tag: "Failure", value: 3 }));
});

test("a DeliverDefect kills the fiber without a release", () => {
  const { log, runTask } = started(durable(run));
  runTask({ _tag: "DeliverDefect", fiber: fiberId(0), token: token(0) });
  expect(log.slice(1)).toEqual(rootEnd({ _tag: "Defect" }));
});

// Review Focus 3, unmasked: the release is the callback's cleanup, so it
// comes before the finalizer's own events, and the await is then over.
test("an interrupted await releases before its finalizer runs", () => {
  const { log, runTask } = started(Effect.ensuring(
    durable(run),
    Effect.ignore(durable(sleep)),
  ));
  runTask(interruptRoot);
  expect(log).toEqual([start(0, 0, run), release(0, 0), start(0, 1, sleep)]);
  runTask(deliver(0, 0, value(5)));
  expect(log.length).toBe(3);
  runTask(deliver(0, 1, value(0)));
  expect(log.slice(3)).toEqual(rootEnd({ _tag: "Interrupted" }));
});

// Review Focus 3, masked: the interrupt waits for the mask's end, so the
// await reports no release and the delivery reaches the continuation.
test("a masked await is not released and takes its delivery", () => {
  const seen: number[] = [];
  const remember = (amount: number) => Effect.sync(() => {
    seen.push(amount);
  });
  const { log, runTask } = started(Effect.ensuring(
    Effect.uninterruptible(Effect.flatMap(durable(run), remember)),
    Effect.ignore(durable(sleep)),
  ));
  runTask(interruptRoot);
  expect(log).toEqual([start(0, 0, run)]);
  runTask(deliver(0, 0, value(5)));
  expect(seen).toEqual([5]);
  expect(log).toEqual([start(0, 0, run), start(0, 1, sleep)]);
  runTask(deliver(0, 1, value(0)));
  expect(log.slice(2)).toEqual(rootEnd({ _tag: "Interrupted" }));
});

const cancelled = (program: Effect.Effect<unknown, unknown, Durable>) => {
  const { log, runTask } = started(program);
  runTask(cancel(0, 0));
  return log;
};

test("a DeliverCancel releases the await, masked or not", () => {
  const expected = [
    start(0, 0, run),
    release(0, 0),
    ...rootEnd({ _tag: "Interrupted" }),
  ];
  expect(cancelled(durable(run))).toEqual(expected);
  expect(cancelled(Effect.uninterruptible(durable(run)))).toEqual(expected);
});

test("each await has its own token, and each token is used once", () => {
  const { log, runTask } = started(Effect.all([durable(run), durable(run)], {
    concurrency: "unbounded",
  }));
  const starts: Event[] = log.filter((event) => event._tag === "Start");
  expect(starts).toEqual([start(1, 0, run), start(2, 1, run)]);
  runTask(deliver(1, 0, value(1)));
  const settled = log.length;
  runTask(deliver(1, 0, value(9)));
  runTask(cancel(1, 0));
  runTask(deliver(1, 1, value(9)));
  expect(log.length).toBe(settled);
  runTask(deliver(2, 1, value(2)));
  expect(log.at(-1)).toEqual(exitWith({ _tag: "Success", value: 0 }));
});

test("a delivery after a release changes nothing", () => {
  const { log, runTask } = started(durable(run));
  runTask(cancel(0, 0));
  const settled = log.length;
  runTask(deliver(0, 0, value(1)));
  runTask(cancel(0, 0));
  expect(log.length).toBe(settled);
});

// A fiber under PreventSchedulerYield never reaches shouldYield, so it is
// never registered; its await has no fiber id to report and dies instead.
test("an await on an unregistered fiber dies without a Start", () => {
  const child = Effect.flatMap(Effect.forkChild(durable(run)), Fiber.join);
  const { log, runTask } = started(Effect.provideService(
    child,
    Scheduler.PreventSchedulerYield,
    true,
  ));
  drain(runTask, log);
  expect(log.filter((event) => event._tag === "Start")).toEqual([]);
  expect(log.at(-1)).toEqual(exitWith({ _tag: "Defect" }));
});

// Effect's callback already ignores a second resume; the adapter forgets
// the resume too, so a finished await holds nothing.
test("an await is forgotten once resumed or released", () => {
  const state = makeState();
  const host = loggingHost([]);
  state.register = registration(state, host);
  const program = Effect.flatMap(durable(run), () => durable(run));
  Effect.runFork(
    Effect.provideService(program, Durable, makeDurable(state, host)),
    { scheduler: deterministicScheduler(state, host) },
  );
  answer(state, { _tag: "Deliver", ...deliveredTo(0, 0) });
  expect([...state.awaits.keys()]).toEqual([token(1)]);
  requestInterrupt(state, fiberId(0));
  expect([...state.awaits.keys()]).toEqual([]);
});
