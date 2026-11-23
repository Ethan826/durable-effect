import assert from "node:assert/strict";
import { test } from "node:test";
import { makeAdapter } from "../src/adapter/Runtime.ts";
import type { Program, Sequence, Statement } from "./grammar.ts";
import { scriptedHost } from "./host.ts";
import type { Journal, LogEntry } from "./host.ts";
import { interpret } from "./interpret.ts";

const valueJournal: Journal = {
  outcomes: [{ _tag: "Value", value: 1 }],
  cancelBefore: undefined,
};

const runProgram = (program: Program, journal = valueJournal) => {
  const host = scriptedHost(journal, { seed: 7 });
  host.run(makeAdapter(interpret(program), 0, host));
  return host.log;
};

/** How the run ended: the root's exit tag, or `Blocked`. */
const endOf = (log: ReadonlyArray<LogEntry>): string =>
  log.flatMap((entry) =>
    entry._tag === "Emitted" && entry.event._tag === "RootExit"
      ? [entry.event.exit._tag]
      : entry._tag === "Blocked" ? ["Blocked"] : []
  ).join(",");

const sleepsIn = (log: ReadonlyArray<LogEntry>) => log.flatMap((entry) =>
  entry._tag === "Emitted" && entry.event._tag === "Start" &&
    entry.event.op._tag === "Sleep"
    ? [entry.event.op.duration]
    : []
);

const root = (statements: Sequence, forks: Sequence[] = []): Program =>
  ({ root: statements, forks });

const cases: ReadonlyArray<readonly [Statement[], string]> = [
  [[{ _tag: "Run", kind: 2 }], "Success"],
  [[{ _tag: "Call" }], "Success"],
  [[{ _tag: "Fail", caught: true }], "Success"],
  [[{ _tag: "Fail", caught: false }], "Failure"],
  [[{ _tag: "Die", caught: true }], "Success"],
  [[{ _tag: "Die", caught: false }], "Defect"],
  [[{ _tag: "Retry", count: 2049 }], "Success"],
  [[{ _tag: "RetrySpaced", steps: 3, jittered: true }], "Success"],
  [[{ _tag: "Timeout", count: 5000, millis: 1 }], "Success"],
  [[{ _tag: "RaceDurable", count: 1, kind: 0 }], "Success"],
  [[{ _tag: "All", counts: [5000, 1], durable: true, concurrency: 2 }],
    "Success"],
  [[{ _tag: "ForEach", counts: [5000, 2049, 1, 2, 1, 1, 1, 1] }], "Success"],
  [[{ _tag: "Never" }], "Blocked"],
  [[{ _tag: "Deadlock" }], "Blocked"],
  [[{ _tag: "DeferredAwait", deferred: 0 }], "Blocked"],
  [[{ _tag: "QueueTake" }], "Blocked"],
  [[{ _tag: "DeferredSucceed", deferred: 1 },
    { _tag: "DeferredAwait", deferred: 1 }], "Success"],
  [[{ _tag: "QueueOffer" }, { _tag: "QueueTake" }], "Success"],
];

test("each statement ends as its Effect combinator does", () => {
  const ends = cases.map(([statements]) => endOf(runProgram(root(statements))));
  assert.deepEqual(ends, cases.map(([, expected]) => expected));
});

test("a zero-delay repeat or retry of N steps sleeps N - 1 times", () => {
  const repeat = runProgram(root([{ _tag: "Repeat", count: 2049 }]));
  const retry = runProgram(root([{ _tag: "Retry", count: 2 }]));
  assert.equal(sleepsIn(repeat).length, 2048);
  assert.deepEqual(sleepsIn(retry), [{ _tag: "Millis", millis: 0 }]);
});

test("a spaced schedule of three steps sleeps twice, at least 1 ms", () => {
  const plain: Statement = { _tag: "RepeatSpaced", steps: 3, jittered: false };
  assert.deepEqual(sleepsIn(runProgram(root([plain]))), [
    { _tag: "Millis", millis: 1 },
    { _tag: "Millis", millis: 1 },
  ]);
});

test("a fork runs its body once; join waits for it", () => {
  const forks = [[{ _tag: "Run", kind: 1 }]] satisfies Sequence[];
  const twice: Sequence = [
    { _tag: "Fork", fiber: 0, detach: false },
    { _tag: "Fork", fiber: 0, detach: true },
    { _tag: "Join", fiber: 0 },
  ];
  const log = runProgram(root(twice, forks));
  const starts = log.filter((entry) =>
    entry._tag === "Emitted" && entry.event._tag === "Start"
  );
  assert.equal(starts.length, 1);
  assert.equal(endOf(log), "Success");
});

test("a finalizer runs after its body fails", () => {
  const ensuring: Statement = {
    _tag: "Ensuring",
    body: [{ _tag: "Fail", caught: false }],
    finalizer: [{ _tag: "Run", kind: 0 }],
  };
  const log = runProgram(root([ensuring]));
  assert.equal(endOf(log), "Failure");
  assert.equal(sleepsIn(log).length, 0);
  assert.ok(log.some((entry) =>
    entry._tag === "Sent" && entry.task._tag === "Deliver"
  ));
});

test("a cancel interrupts a fiber awaiting inside a mask", () => {
  const masked: Statement = {
    _tag: "Uninterruptible", body: [{ _tag: "Run", kind: 0 }],
  };
  const cancelFirst = { ...valueJournal, cancelBefore: 0 };
  assert.equal(endOf(runProgram(root([masked]), cancelFirst)), "Interrupted");
});
