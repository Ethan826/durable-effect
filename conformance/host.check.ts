import assert from "node:assert/strict";
import { test } from "node:test";
import { Brand, Clock, Duration, Effect, Random } from "effect";
import { durable } from "../src/adapter/Durable.ts";
import type { Durable } from "../src/adapter/Durable.ts";
import type {
  FiberId,
  Op,
  Outcome,
  RootExit,
  Task,
} from "../src/adapter/Interface.ts";
import { makeAdapter } from "../src/adapter/Runtime.ts";
import { scriptedHost } from "./host.ts";
import type { Journal } from "./deliveries.ts";
import type { LogEntry, ScriptedHost } from "./host.ts";

const run: Op = { _tag: "Run", kind: 1, args: 0 };
const value = (amount: number): Outcome => ({ _tag: "Value", value: amount });
const failure = (amount: number): Outcome =>
  ({ _tag: "Failure", value: amount });
const script = (
  outcomes: ReadonlyArray<Outcome>,
  cancelBefore?: number,
): Journal => ({ outcomes, cancelBefore });

type Program = Effect.Effect<unknown, unknown, Durable>;

/** Runs `build(host)` under a fresh scripted host; answers the host. */
const runWith = (
  journal: Journal,
  build: (host: ScriptedHost) => Program,
  seed = 1,
) => {
  const host = scriptedHost(journal, { seed });
  host.run(makeAdapter(build(host), 0, host));
  return host;
};

const sentTags = (log: ReadonlyArray<LogEntry>) => log.flatMap((entry) =>
  entry._tag === "Sent" ? [entry.task._tag] : []
);
const rootExit = (log: ReadonlyArray<LogEntry>) => log.flatMap((entry) =>
  entry._tag === "Emitted" && entry.event._tag === "RootExit"
    ? [entry.event.exit]
    : []
);
const exitOf = (exit: RootExit) => [exit];

test("starts the root, then delivers the scripted outcome", () => {
  const host = runWith(script([value(2)]), () => durable(run));
  assert.deepEqual(sentTags(host.log), ["StartRoot", "Deliver"]);
  assert.deepEqual(rootExit(host.log), exitOf({ _tag: "Success", value: 2 }));
});

test("outcomes go to tokens in order, and Failure fails", () => {
  const twice = Effect.andThen(durable(run), durable(run));
  const host = runWith(script([value(0), failure(2)]), () => twice);
  assert.deepEqual(rootExit(host.log), exitOf({ _tag: "Failure", value: 2 }));
});

test("the journal repeats from its start when tokens outrun it", () => {
  const three = Effect.andThen(durable(run), durable(run)).pipe(
    Effect.andThen(durable(run)),
  );
  const host = runWith(script([value(1), value(2)]), () => three);
  assert.deepEqual(rootExit(host.log), exitOf({ _tag: "Success", value: 1 }));
});

test("a cancel before notification 1 goes to the fiber awaiting then", () => {
  const twice = Effect.andThen(durable(run), durable(run));
  const host = runWith(script([value(0), value(1)], 1), () => twice);
  assert.deepEqual(sentTags(host.log), [
    "StartRoot", "Deliver", "DeliverCancel",
  ]);
  assert.deepEqual(rootExit(host.log), exitOf({ _tag: "Interrupted" }));
});

test("FIFO: queued tasks run before any delivery", () => {
  const program = Effect.andThen(Effect.yieldNow, durable(run));
  const host = runWith(script([value(0)]), () => program);
  assert.deepEqual(sentTags(host.log), ["StartRoot", "RunQueued", "Deliver"]);
});

test("nothing queued or awaited before the root exits: blocked", () => {
  const host = runWith(script([value(0)]), () => Effect.never);
  assert.deepEqual(host.log.at(-1), { _tag: "Blocked" });
  assert.deepEqual(rootExit(host.log), []);
});

test("after the root exits it interrupts live fibers and delivers nothing",
  () => {
    const child = Effect.andThen(Effect.forkDetach(durable(run)),
      Effect.yieldNow);
    const host = runWith(script([value(0)]), () => child);
    const tags = sentTags(host.log);
    assert.deepEqual(tags.slice(-1), ["RequestInterrupt"]);
    assert.ok(!tags.includes("Deliver"));
    assert.ok(host.log.some((entry) =>
      entry._tag === "Emitted" && entry.event._tag === "Release"
    ));
  });

test("register answers false while running and true while closing", () => {
  const late = Effect.forkDetach(Effect.void).pipe(
    Effect.andThen(Effect.yieldNow),
    Effect.andThen(Effect.forkDetach(Effect.void)),
  );
  const host = runWith(script([value(0)]), () => late);
  const answers = host.log.flatMap((entry) =>
    entry._tag === "Answered" && entry.question === "register"
      ? [entry.answer]
      : []
  );
  assert.deepEqual(answers, [false, false, true]);
});

test("the clock answers the number of deliveries so far", () => {
  const program = Effect.andThen(durable(run), Clock.currentTimeMillis).pipe(
    Effect.flatMap((before) =>
      Effect.andThen(durable(run), Effect.map(Clock.currentTimeMillis,
        (after) => before * 10 + after))
    ),
  );
  const host = runWith(script([value(0)]), () => program);
  assert.deepEqual(rootExit(host.log), exitOf({ _tag: "Success", value: 12 }));
});

const drawsOf = (seed: number) => {
  const host = runWith(script([value(0)]), () =>
    Effect.all([Random.next, Random.next]), seed);
  return host.log.flatMap((entry) =>
    entry._tag === "Answered" && entry.question === "draw"
      ? [entry.answer]
      : []
  );
};

test("draws come from the seed: the same seed gives the same draws", () => {
  assert.equal(drawsOf(3).length, 2);
  assert.deepEqual(drawsOf(3), drawsOf(3));
  assert.notDeepEqual(drawsOf(3), drawsOf(4));
});

test("inSlice is true only inside runTask", () => {
  let inside = false;
  const host = runWith(script([value(0)]), (scripted) =>
    Effect.sync(() => {
      inside = scripted.inSlice();
    }));
  assert.equal(inside, true);
  assert.equal(host.inSlice(), false);
});

test("the log holds each task sent and each event, in order", () => {
  const host = runWith(script([value(2)]), () => durable(run));
  assert.deepEqual(host.log.map((entry) => entry._tag), [
    "Sent", "Answered", "Emitted", "Sent", "Emitted", "Emitted",
  ]);
});

test("a Sleep token receives Value whatever the journal holds", () => {
  const program = Effect.andThen(Effect.sleep("1 millis"), durable(run));
  const host = runWith(script([failure(2), failure(1)]), () => program);
  const outcomes = host.log.flatMap((entry) =>
    entry._tag === "Sent" && entry.task._tag === "Deliver"
      ? [entry.task.outcome]
      : []
  );
  assert.deepEqual(outcomes, [value(0), failure(2)]);
  assert.deepEqual(rootExit(host.log), exitOf({ _tag: "Failure", value: 2 }));
});

const forever = Effect.sleep(Duration.infinity);

test("a Sleep Forever is never delivered a Value: the run blocks", () => {
  const host = runWith(script([value(0)]), () => forever);
  assert.deepEqual(sentTags(host.log), ["StartRoot"]);
  assert.deepEqual(host.log.at(-1), { _tag: "Blocked" });
  assert.deepEqual(rootExit(host.log), []);
});

test("a run beside a Sleep Forever is delivered, then the run blocks", () => {
  const both = Effect.all([forever, durable(run)], {
    concurrency: "unbounded",
  });
  const host = runWith(script([value(1)]), () => both);
  const delivered = host.log.flatMap((entry) =>
    entry._tag === "Sent" && entry.task._tag === "Deliver"
      ? [entry.task.outcome]
      : []
  );
  assert.deepEqual(delivered, [value(1)]);
  assert.deepEqual(host.log.at(-1), { _tag: "Blocked" });
});

test("a cancel ends a Sleep Forever", () => {
  const host = runWith(script([value(0)], 0), () => forever);
  assert.deepEqual(sentTags(host.log), ["StartRoot", "DeliverCancel"]);
  assert.deepEqual(rootExit(host.log), exitOf({ _tag: "Interrupted" }));
});

test("an operation started while closing is answered with a defect", () => {
  const child = Effect.ensuring(Effect.never, Effect.ignore(durable(run)));
  const program = Effect.andThen(Effect.forkDetach(child), Effect.yieldNow);
  const host = runWith(script([value(0)]), () => program);
  const tags = sentTags(host.log);
  assert.deepEqual(tags.slice(tags.indexOf("RequestInterrupt")), [
    "RequestInterrupt", "DeliverDefect",
  ]);
  assert.ok(!tags.includes("Deliver"));
  assert.ok(host.log.some((entry) =>
    entry._tag === "Emitted" && entry.event._tag === "FiberExited" &&
    entry.event.fiber !== 0
  ));
});

test("runPaced logs what run logs, pausing after every step", async () => {
  const program = Effect.andThen(Effect.yieldNow, durable(run));
  const plain = runWith(script([value(1)]), () => program);
  const paced = scriptedHost(script([value(1)]), { seed: 1 });
  const pauses: number[] = [];
  const pause = async (steps: number) => {
    pauses.push(steps);
  };
  await paced.runPaced(makeAdapter(program, 0, paced), pause);
  assert.deepEqual(paced.log, plain.log);
  // StartRoot, RunQueued, Deliver, then the step that enters closing.
  assert.deepEqual(pauses, [1, 2, 3, 4]);
});

test("extend sends one more task inside a slice, and logs it", () => {
  const host = scriptedHost(script([value(0)]), { seed: 1 });
  let inside = false;
  const noteSlice = Effect.sync(() => {
    inside = host.inSlice();
  });
  const adapter = makeAdapter(Effect.ensuring(Effect.never, noteSlice), 0,
    host);
  host.run(adapter);
  const before = host.log.length;
  const interrupt: Task = {
    _tag: "RequestInterrupt",
    fiber: Brand.nominal<FiberId>()(0),
  };
  host.extend(adapter, interrupt);
  assert.deepEqual(host.log[before], { _tag: "Sent", task: interrupt });
  assert.deepEqual(rootExit(host.log), exitOf({ _tag: "Interrupted" }));
  assert.equal(inside, true);
});
