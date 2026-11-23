import assert from "node:assert/strict";
import { test } from "node:test";
import { Effect } from "effect";
import fc from "fast-check";
import { makeAdapter } from "../src/adapter/Runtime.ts";
import { journal, program } from "./grammar.ts";
import type { Program, Statement } from "./grammar.ts";
import { scriptedHost } from "./host.ts";
import type { Journal } from "./host.ts";
import { interpret } from "./interpret.ts";

// The dossier's statement kinds, listed here by hand so that the test does
// not read them from the grammar it checks.
const statementKinds = [
  "Run", "Sleep", "ClockRead", "RandomDraw", "YieldNow", "Loop", "Repeat",
  "Retry", "Timeout", "RacePure", "RaceDurable", "Fail", "Die",
  "RetrySpaced", "RepeatSpaced", "Timed", "DateTimeNow", "Log", "FnSpan",
  "Call", "Never", "Deadlock", "All", "ForEach", "Cached", "RefUpdate",
  "RefGet", "DeferredSucceed", "DeferredAwait", "QueueOffer", "QueueTake",
  "Fork", "Join", "Interrupt", "Poll", "Uninterruptible", "Ensuring",
  "AcquireRelease",
];
const loopCounts = [1, 2, 2049, 5000];
const blockingKinds = new Set([
  "Never", "Deadlock", "DeferredAwait", "QueueTake",
]);
const sampleCount = 1000;
const runCount = 1000;

const isStatement = (value: unknown): value is Statement =>
  typeof value === "object" && value !== null && "_tag" in value;

/** Every statement held directly in one of the statement's fields. */
const childrenOf = (statement: Statement): ReadonlyArray<Statement> =>
  Object.values(statement).filter(Array.isArray).flat().filter(isStatement);

/** The statement and everything nested in it, outermost first. */
const flatten = (statement: Statement): ReadonlyArray<Statement> =>
  [statement, ...childrenOf(statement).flatMap(flatten)];

const allStatements = (sample: Program): ReadonlyArray<Statement> =>
  [sample.root, ...sample.forks].flat().flatMap(flatten);

/** Levels of statements: a leaf is 1, a container one more than its own. */
const nesting = (statement: Statement): number =>
  1 + Math.max(0, ...childrenOf(statement).map(nesting));

const countsIn = (statement: Statement): ReadonlyArray<unknown> =>
  Object.entries(statement).flatMap(([field, value]) =>
    ["count", "left", "right", "counts"].includes(field) ? [value] : []
  ).flat();

const samples = fc.sample(program, { seed: 1, numRuns: sampleCount });
const statements = samples.flatMap(allStatements);

test("over 1,000 samples every statement kind occurs", () => {
  const seen = new Set<string>(statements.map((one) => one._tag));
  assert.deepEqual(statementKinds.filter((kind) => !seen.has(kind)), []);
  assert.equal(seen.size, statementKinds.length);
});

test("over 1,000 samples every loop count occurs, and no other", () => {
  const seen = new Set(statements.flatMap(countsIn));
  assert.deepEqual([...seen].sort((a, b) => Number(a) - Number(b)), loopCounts);
});

test("nesting never exceeds 3, and reaches it", () => {
  const depths = samples.map((sample) =>
    Math.max(...[sample.root, ...sample.forks].flat().map(nesting))
  );
  assert.equal(Math.max(...depths), 3);
});

test("a program has up to three forks of one to six statements", () => {
  const forkCounts = new Set(samples.map((sample) => sample.forks.length));
  assert.deepEqual([...forkCounts].sort(), [0, 1, 2, 3]);
  const lengths = samples.flatMap((sample) =>
    [sample.root, ...sample.forks].map((body) => body.length)
  );
  assert.equal(Math.min(...lengths), 1);
  assert.equal(Math.max(...lengths), 6);
});

test("forEach takes 1 to 8 elements; a finalizer 1 or 2 statements", () => {
  const widths = statements.flatMap((statement) =>
    statement._tag === "ForEach" ? [statement.counts.length] : []
  );
  assert.equal(Math.min(...widths), 1);
  assert.equal(Math.max(...widths), 8);
  const finalizers = statements.flatMap((statement) =>
    statement._tag === "Ensuring" ? [statement.finalizer.length] : []
  );
  assert.deepEqual([...new Set(finalizers)].sort(), [1, 2]);
});

test("journal values are in {0, 1, 2}; a cancel is absent or 0 to 3", () => {
  const journals = fc.sample(journal, { seed: 1, numRuns: sampleCount });
  const values = journals.flatMap((one) =>
    one.outcomes.map((outcome) => outcome.value)
  );
  assert.deepEqual([...new Set(values)].sort(), [0, 1, 2]);
  const cancels = new Set(journals.map((one) => one.cancelBefore));
  assert.deepEqual([...cancels].map(String).sort(), [
    "0", "1", "2", "3", "undefined",
  ]);
});

/** Runs a program under the scripted host; answers the host's log. */
const runUnderHost = (sample: Program, script: Journal) => {
  const host = scriptedHost(script, { seed: 7 });
  host.run(makeAdapter(interpret(sample), 0, host));
  return host.log;
};

const ended = (log: ReturnType<typeof runUnderHost>) => ({
  exited: log.some((entry) =>
    entry._tag === "Emitted" && entry.event._tag === "RootExit"
  ),
  blocked: log.some((entry) => entry._tag === "Blocked"),
});

const canBlock = (sample: Program) =>
  allStatements(sample).some((statement) => blockingKinds.has(statement._tag));

test("a sample runs to an exit, or blocks only where it can", () => {
  fc.assert(
    fc.property(program, journal, (sample, script) => {
      const end = ended(runUnderHost(sample, script));
      assert.notEqual(end.exited, end.blocked);
      if (!canBlock(sample)) assert.ok(end.exited);
    }),
    { seed: 1, numRuns: runCount },
  );
});

const onlyRoot = (root: ReadonlyArray<Statement>): Program =>
  ({ root, forks: [] });
const valueJournal: Journal = {
  outcomes: [{ _tag: "Value", value: 1 }],
  cancelBefore: undefined,
};

test("Effect.never and the two-fiber deadlock end blocked", () => {
  const never = runUnderHost(onlyRoot([{ _tag: "Never" }]), valueJournal);
  assert.deepEqual(ended(never), { exited: false, blocked: true });
  const deadlock = runUnderHost(onlyRoot([{ _tag: "Deadlock" }]), valueJournal);
  assert.deepEqual(ended(deadlock), { exited: false, blocked: true });
});

test("a program interprets to an Effect", () => {
  assert.ok(Effect.isEffect(interpret(onlyRoot([{ _tag: "YieldNow" }]))));
});
