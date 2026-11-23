import { expect, test } from "bun:test";
import { Brand, Effect } from "effect";
import type {
  Event,
  FiberId,
  Host,
  Task,
  TaskId,
} from "../../src/adapter/Interface.ts";
import { makeAdapter } from "../../src/adapter/Runtime.ts";

/** A host event or a registration question, in the order they happened. */
type Entry = Event | { readonly _tag: "Register"; readonly fiber: number };

/** A host that logs everything and answers `register` from a function. */
const loggingHost = (
  log: Entry[],
  answer: (fiber: FiberId) => boolean = () => false,
): Host => ({
  emit: (event) => {
    log.push(event);
  },
  clock: () => 0,
  draw: () => 0,
  register: (fiber) => {
    log.push({ _tag: "Register", fiber });
    return answer(fiber);
  },
  inSlice: () => true,
  foreign: () => {},
});

const startRoot: Task = { _tag: "StartRoot" };
const taskId = Brand.nominal<TaskId>();

/** Sends `RunQueued` for every `Queue` in the log, oldest first. */
const drain = (runTask: (task: Task) => void, log: Entry[]) => {
  let seen = 0;
  while (seen < log.length) {
    const entry = log[seen++];
    if (entry?._tag === "Queue") {
      runTask({ _tag: "RunQueued", task: entry.task });
    }
  }
};

/** Sends `RunQueued` for an entry if it is a `Queue`. */
const runEntry = (runTask: (task: Task) => void, entry?: Entry) => {
  if (entry?._tag === "Queue") {
    runTask({ _tag: "RunQueued", task: entry.task });
  }
};

const tags = (log: Entry[]) =>
  log.map((entry) => ("fiber" in entry ? `${entry._tag} ${entry.fiber}`
    : entry._tag));

test("the root registers first", () => {
  const log: Entry[] = [];
  makeAdapter(Effect.succeed(1), 0, loggingHost(log)).runTask(startRoot);
  expect(log[0]).toEqual({ _tag: "Register", fiber: 0 });
});

test("a second StartRoot does nothing", () => {
  const log: Entry[] = [];
  const adapter = makeAdapter(Effect.succeed(1), 0, loggingHost(log));
  adapter.runTask(startRoot);
  const first = log.length;
  adapter.runTask(startRoot);
  expect(log.length).toBe(first);
});

test("RootExit follows the root's FiberExited", () => {
  const log: Entry[] = [];
  makeAdapter(Effect.succeed(7), 0, loggingHost(log)).runTask(startRoot);
  expect(tags(log)).toEqual(["Register 0", "FiberExited 0", "RootExit"]);
  expect(log[2]).toEqual({
    _tag: "RootExit",
    exit: { _tag: "Success", value: 7 },
  });
});

const forkThenWait = Effect.flatMap(
  Effect.forkChild(Effect.void),
  () => Effect.never,
);

test("a queued fork registers when its task runs, not at fork", () => {
  const log: Entry[] = [];
  const adapter = makeAdapter(forkThenWait, 0, loggingHost(log));
  adapter.runTask(startRoot);
  expect(tags(log)).toEqual(["Register 0", "Queue"]);
  drain(adapter.runTask, log);
  expect(tags(log)).toEqual([
    "Register 0", "Queue", "Register 1", "FiberExited 1",
  ]);
});

// A fork's queued task starts the child from scratch, so running it a
// second time would repeat the child's first step.
test("RunQueued runs a task once and ignores an unknown one", () => {
  const log: Entry[] = [];
  let steps = 0;
  const child = Effect.andThen(Effect.sync(() => steps++), Effect.never);
  const program = Effect.andThen(Effect.forkChild(child), Effect.never);
  const adapter = makeAdapter(program, 0, loggingHost(log));
  adapter.runTask(startRoot);
  runEntry(adapter.runTask, log[1]);
  runEntry(adapter.runTask, log[1]);
  adapter.runTask({ _tag: "RunQueued", task: taskId(99) });
  expect(steps).toBe(1);
  expect(tags(log)).toEqual(["Register 0", "Queue", "Register 1"]);
});

// Review Focus 1: forEach forks each element inside the forking task.
// An element that is already an exit is not forked, so each one syncs.
test("a concurrent forEach registers its children in one task", () => {
  const log: Entry[] = [];
  const element = (value: number) => Effect.sync(() => value);
  const program = Effect.forEach([1, 2, 3, 4, 5], element, {
    concurrency: "unbounded",
  });
  makeAdapter(program, 0, loggingHost(log)).runTask(startRoot);
  const registered = log.filter((entry) => entry._tag === "Register");
  expect(registered.length).toBe(6);
  expect(log.filter((entry) => entry._tag === "Queue")).toEqual([]);
  expect(log.at(-1)?._tag).toBe("RootExit");
});

/**
 * A root that detaches `child` and exits. Every fiber but the root is asked
 * to be interrupted, as during closing.
 */
const closingAdapter = (log: Entry[], child: Effect.Effect<void>) =>
  makeAdapter(
    Effect.asVoid(Effect.forkDetach(child)),
    0,
    loggingHost(log, (fiber) => fiber !== 0),
  );

const closingPrefix = ["Register 0", "Queue", "FiberExited 0", "RootExit"];

// Review Focus 2: a fork still queued at the root's exit is never
// registered; run during closing, it is interrupted before its first step.
// Effect queues a resume before the interrupt fires; that task does nothing.
test("a fork queued at the root's exit takes no step of its own", () => {
  const log: Entry[] = [];
  let stepped = false;
  const adapter = closingAdapter(log, Effect.sync(() => {
    stepped = true;
  }));
  adapter.runTask(startRoot);
  expect(tags(log)).toEqual(closingPrefix);
  runEntry(adapter.runTask, log[1]);
  const own = tags(log.slice(4)).filter((tag) => tag !== "Queue");
  expect(own).toEqual(["Register 1", "FiberExited 1"]);
  const settled = log.length;
  drain(adapter.runTask, log);
  expect(log.length).toBe(settled);
  expect(stepped).toBe(false);
});

// A fiber that starts masked cannot be interrupted before its first step:
// the request waits until the mask ends (Effect's semantics; X6.3 asks only
// that the executor request it).
test("a masked fork in closing runs until its mask ends", () => {
  const log: Entry[] = [];
  const steps: string[] = [];
  const step = (name: string) => Effect.sync(() => {
    steps.push(name);
  });
  const child = Effect.andThen(
    step("masked"),
    Effect.interruptible(step("after")),
  );
  const adapter = makeAdapter(
    Effect.asVoid(Effect.forkDetach(child, { uninterruptible: true })),
    0,
    loggingHost(log, (fiber) => fiber !== 0),
  );
  adapter.runTask(startRoot);
  drain(adapter.runTask, log);
  expect(steps).toEqual(["masked"]);
  expect(tags(log).at(-1)).toBe("FiberExited 1");
});

test("a yielding finalizer's events come before RootExit", () => {
  const log: Entry[] = [];
  const program = Effect.ensuring(Effect.succeed(3), Effect.yieldNow);
  const adapter = makeAdapter(program, 0, loggingHost(log));
  adapter.runTask(startRoot);
  expect(tags(log)).toEqual(["Register 0", "Queue"]);
  drain(adapter.runTask, log);
  expect(tags(log)).toEqual([
    "Register 0", "Queue", "FiberExited 0", "RootExit",
  ]);
});

test("a failed root reports its error value", () => {
  const log: Entry[] = [];
  makeAdapter(Effect.fail(4), 0, loggingHost(log)).runTask(startRoot);
  expect(log.at(-1)).toEqual({
    _tag: "RootExit",
    exit: { _tag: "Failure", value: 4 },
  });
});

test("a root's value that is not a natural reports Success 0", () => {
  const values: ReadonlyArray<unknown> = [undefined, { a: 1 }];
  const exits = values.map((value) => {
    const log: Entry[] = [];
    makeAdapter(Effect.succeed(value), 0, loggingHost(log))
      .runTask(startRoot);
    return log.at(-1);
  });
  const success: Entry = {
    _tag: "RootExit",
    exit: { _tag: "Success", value: 0 },
  };
  expect(exits).toEqual([success, success]);
});

test("a defect reports Defect and an interruption Interrupted", () => {
  const exitOf = (program: Effect.Effect<unknown, unknown>) => {
    const log: Entry[] = [];
    makeAdapter(program, 0, loggingHost(log)).runTask(startRoot);
    return log.at(-1);
  };
  expect(exitOf(Effect.die("boom"))).toEqual({
    _tag: "RootExit",
    exit: { _tag: "Defect" },
  });
  expect(exitOf(Effect.interrupt)).toEqual({
    _tag: "RootExit",
    exit: { _tag: "Interrupted" },
  });
});
