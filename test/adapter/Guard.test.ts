import { expect, test } from "bun:test";
import { Brand, Context, Effect, Fiber } from "effect";
import { durable } from "../../src/adapter/Durable.ts";
import type { Durable } from "../../src/adapter/Durable.ts";
import { guardInterrupt } from "../../src/adapter/Guard.ts";
import type {
  Event,
  FiberId,
  Host,
  Task,
  Token,
} from "../../src/adapter/Interface.ts";
import { makeAdapter } from "../../src/adapter/Runtime.ts";
import type { AnyFiber } from "../../src/adapter/State.ts";

const fiberId = Brand.nominal<FiberId>();
type Foreign = readonly [string, FiberId];

/** A host whose `inSlice` is true only while `runTask` is running. */
const slicedHost = (log: Event[], foreign: Foreign[]) => {
  const state = { inside: false };
  const host: Host = {
    emit: (event) => {
      log.push(event);
    },
    clock: () => 0,
    draw: () => 0,
    register: () => false,
    inSlice: () => state.inside,
    foreign: (kind, fiber) => {
      foreign.push([kind, fiber]);
    },
    noteGlobal: () => {},
  };
  return { host, state };
};

/** Runs the adapter's tasks with `inSlice` true, then restores false. */
const sliced = (
  state: { inside: boolean },
  runTask: (task: Task) => void,
) => (task: Task) => {
  state.inside = true;
  try {
    runTask(task);
  } finally {
    state.inside = false;
  }
};

/** Runs every queued task, oldest first, including ones queued meanwhile. */
const drain = (log: Event[], run: (task: Task) => void) => {
  let seen = 0;
  while (seen < log.length) {
    const entry = log[seen++];
    if (entry?._tag === "Queue") run({ _tag: "RunQueued", task: entry.task });
  }
};

type Calls = Array<readonly [unknown, unknown]>;

test("inside a slice the guard forwards its arguments to the original", () => {
  const calls: Calls = [];
  const foreign: Foreign[] = [];
  const { host, state } = slicedHost([], foreign);
  const original: AnyFiber["interruptUnsafe"] = (id, annotations) => {
    calls.push([id, annotations]);
  };
  const annotations = Context.empty();
  state.inside = true;
  guardInterrupt(fiberId(3), original, host)(9, annotations);
  expect(calls).toEqual([[9, annotations]]);
  expect(foreign).toEqual([]);
});

test("outside a slice the guard reports foreign and does not forward", () => {
  const calls: Calls = [];
  const foreign: Foreign[] = [];
  const { host } = slicedHost([], foreign);
  const original: AnyFiber["interruptUnsafe"] = (id, annotations) => {
    calls.push([id, annotations]);
  };
  guardInterrupt(fiberId(3), original, host)(9, Context.empty());
  expect(calls).toEqual([]);
  expect(foreign).toEqual([["interrupt", fiberId(3)]]);
});

type Child = Effect.Effect<void, number, Durable>;
type Out = { fiber?: Fiber.Fiber<void, number> };

/**
 * A root that detaches `child` and hands its fiber out. The child's task is
 * queued, so a test drains it to register the child.
 */
const parent = (child: Child, out: Out, masked = false) =>
  Effect.map(Effect.forkDetach(child, { uninterruptible: masked }), (fiber) => {
    out.fiber = fiber;
  });

/** Starts the program and registers every fiber it queued. */
const started = (program: Effect.Effect<unknown, never, Durable>) => {
  const log: Event[] = [];
  const foreign: Foreign[] = [];
  const { host, state } = slicedHost(log, foreign);
  const run = sliced(state, makeAdapter(program, 0, host).runTask);
  run({ _tag: "StartRoot" });
  drain(log, run);
  return { log, foreign, run };
};

const unwinding = (flag: { unwound: boolean }): Child =>
  Effect.ensuring(Effect.never, Effect.sync(() => {
    flag.unwound = true;
  }));

// Review Focus 4, inside: handler code in a slice interrupts a fiber
// and the target unwinds.
test("Fiber.interrupt from a slice unwinds the target", () => {
  const flag = { unwound: false };
  const out: Out = {};
  const program = Effect.andThen(
    parent(unwinding(flag), out),
    Effect.andThen(Effect.yieldNow, Effect.suspend(() =>
      out.fiber ? Fiber.interrupt(out.fiber) : Effect.void)),
  );
  const { log, foreign } = started(program);
  expect(flag.unwound).toBe(true);
  expect(foreign).toEqual([]);
  expect(log).toContainEqual({ _tag: "FiberExited", fiber: fiberId(1) });
});

// Review Focus 4, outside: a real timer's interrupt is reported and the
// target keeps running.
test("Fiber.interrupt from a timer is foreign and not forwarded", async () => {
  const flag = { unwound: false };
  const out: Out = {};
  const program = Effect.andThen(parent(unwinding(flag), out), Effect.never);
  const { log, foreign } = started(program);
  await new Promise<void>((resolve) => {
    setTimeout(() => {
      if (out.fiber) Effect.runFork(Fiber.interrupt(out.fiber));
      resolve();
    }, 0);
  });
  expect(foreign).toEqual([["interrupt", fiberId(1)]]);
  expect(flag.unwound).toBe(false);
  expect(log).not.toContainEqual({ _tag: "FiberExited", fiber: fiberId(1) });
});

const awaitRun = Effect.asVoid(durable({ _tag: "Run", kind: 1, args: 2 }));
const delivery: Task = {
  _tag: "Deliver",
  fiber: fiberId(1),
  token: Brand.nominal<Token>()(0),
  outcome: { _tag: "Value", value: 5 },
};

/**
 * Interrupts a masked child from outside any slice with the given
 * arguments, delivers its await, and returns the whole trace.
 */
const maskedTrace = (args: Parameters<AnyFiber["interruptUnsafe"]>) => {
  const out: Out = {};
  const program = Effect.andThen(parent(awaitRun, out, true), Effect.never);
  const { log, foreign, run } = started(program);
  out.fiber?.interruptUnsafe(...args);
  run(delivery);
  return { log, foreign };
};

test("a masked fiber interrupted from outside traces the same", () => {
  const plain = maskedTrace([]);
  const loaded = maskedTrace([42, Context.empty()]);
  expect(plain.foreign).toEqual([["interrupt", fiberId(1)]]);
  expect(loaded.foreign).toEqual(plain.foreign);
  expect(loaded.log).toEqual(plain.log);
  expect(plain.log.map((event) => event._tag)).toContain("Start");
  expect(plain.log.at(-1)).toEqual({ _tag: "FiberExited", fiber: fiberId(1) });
});
