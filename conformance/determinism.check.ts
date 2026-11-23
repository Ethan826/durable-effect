import assert from "node:assert/strict";
import { test } from "node:test";
import { evidence } from "./evidence.ts";
import { mutantNames, mutants } from "./mutants.ts";
import type { MutantName } from "./mutants.ts";
import { fullScan, programsPerSeed, runRange, seeds } from "./plan.ts";
import type { Outcome } from "./processes.ts";
import {
  check,
  describe,
  programsCompared,
  properties,
} from "./properties.ts";
import type { Violation } from "./properties.ts";
import { pinnedCases, pinnedJournal } from "./pinned.ts";
import { runCase } from "./runs.ts";
import type { Job, RunResult } from "./runs.ts";

// Properties I1, I2, I7 and I9 of #37, by the dossier's conformance suite:
// seeds 1 to 5, 1,000 programs each; each program in three fresh Node
// processes and once more in a process that has run another program of the
// same seed (plan.ts). Each mutant of #37's table must fail its property
// within that budget. Runs on Node, by `bun run conformance`.

const oneRun = {
  seed: 1, index: 0, role: "fresh0", logHash: "a", furtherHash: "b",
  identities: [0], maxOps: 1, maxLoop: 1, misregistered: 0, statementLoops: 1,
} as const;

test("a crash or a missing run is never a property finding", () => {
  const crash = { results: [], failures: ["worker 1/0/fresh0 ended 3"] };
  const missing = { results: [oneRun], failures: [] };
  assert.equal(check("I1", crash)?.cause, "run");
  assert.equal(check("I1", missing)?.cause, "run");
});

/** I9's finding when the fresh0 run carries `breach`; the rest are clean. */
const i9With = (breach: Partial<RunResult>) => check("I9", {
  failures: [],
  results: [
    { ...oneRun, ...breach }, { ...oneRun, role: "fresh1" },
    { ...oneRun, role: "fresh2" }, { ...oneRun, role: "after" },
  ],
});

test("each of I9's limits is a property finding when passed", () => {
  const breaches: ReadonlyArray<Partial<RunResult>> = [
    { maxLoop: 2050 }, { misregistered: 1 }, { statementLoops: 25 },
    { maxOps: 3_790_849 },
  ];
  assert.deepEqual(breaches.map((breach) => i9With(breach)?.cause),
    ["property", "property", "property", "property"]);
  assert.equal(i9With({}), undefined);
});

test("the scan minimum rejects an empty outcome", () => {
  assert.equal(fullScan({ results: [], failures: [] }), false);
});

const pinnedJob: Job = {
  seed: 0, index: 0, role: "fresh0", pacing: "none", detail: false,
};

/** The old per-task bound, which each pinned case must exceed. */
const refutedBound = 2048 * 9;

test("the pinned I9 cases are the two the dossier records", () => {
  assert.deepEqual(Object.keys(pinnedCases), ["twoWoken", "chain2"]);
});

for (const [name, program] of Object.entries(pinnedCases)) {
  test(`pinned case ${name} meets I9 and exceeds ${refutedBound}`,
    async (context) => {
      const run = await runCase(pinnedJob, [program, pinnedJournal]);
      context.diagnostic(`most operations: in one task ${run.maxOps}, ` +
        `in one run loop ${run.maxLoop}; statement loops ` +
        `${run.statementLoops}`);
      assert.ok(run.maxOps > refutedBound, `${run.maxOps}`);
      assert.equal(check("I9", { results: [
        run, ...(["fresh1", "fresh2", "after"] as const).map((role) =>
          ({ ...run, role })),
      ], failures: [] }), undefined);
    });
}

/** Programs per round when a mutant is run until its property fails. */
const roundSize = 25;

/** The adapter's full budget, run once and shared by the four tests. */
let adapterRuns: Promise<Outcome> | undefined;
const startedAt = performance.now();
const fullBudget = () =>
  adapterRuns ??= runRange(undefined, 0, programsPerSeed);

for (const property of properties) {
  test(`${property} holds for the adapter: seeds 1-5, 1,000 programs each`,
    async (context) => {
      const outcome = await fullBudget();
      const seconds = Math.round((performance.now() - startedAt) / 1000);
      const most = (measure: "maxOps" | "maxLoop" | "statementLoops") =>
        Math.max(...outcome.results.map((run) => run[measure]));
      context.diagnostic(`${outcome.results.length} runs reported; most ` +
        `operations in one task ${most("maxOps")}, in one run loop ` +
        `${most("maxLoop")}; most statement loops in a task ` +
        `${most("statementLoops")}; wall time ${seconds} s`);
      assert.ok(fullScan(outcome), "fewer runs than the full budget");
      assert.equal(programsCompared(property, outcome),
        seeds.length * programsPerSeed);
      const violation = check(property, outcome);
      assert.equal(violation, undefined, describe(violation));
    });
}

/** Runs a mutant round by round until its property fails, or the budget. */
const firstViolation = async (
  mutant: MutantName,
  from = 0,
): Promise<Violation | undefined> => {
  if (from >= programsPerSeed) return undefined;
  const to = Math.min(from + roundSize, programsPerSeed);
  const outcome = await runRange(mutant, from, to);
  return check(mutants[mutant].property, outcome) ??
    firstViolation(mutant, to);
};

for (const mutant of mutantNames) {
  const property = mutants[mutant].property;
  test(`mutant ${mutant} fails ${property} within the budget`,
    async (context) => {
      const violation = await firstViolation(mutant);
      // Only a property finding counts: a crash, a timeout, garbled output
      // or a missing run does not show the property detects the defect.
      assert.equal(violation?.cause, "property", describe(violation) ||
        `${mutant} passed ${property}`);
      if (violation !== undefined) {
        context.diagnostic(await evidence(violation, mutant));
      }
    });
}
