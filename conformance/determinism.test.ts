import assert from "node:assert/strict";
import { test } from "node:test";
import { evidence } from "./evidence.ts";
import { mutantNames, mutants } from "./mutants.ts";
import type { MutantName } from "./mutants.ts";
import { programsPerSeed, runRange } from "./plan.ts";
import type { Outcome } from "./processes.ts";
import { check, describe, properties } from "./properties.ts";
import type { Violation } from "./properties.ts";

// Properties I1, I2, I7 and I9 of #37, by the dossier's conformance suite:
// seeds 1 to 5, 1,000 programs each; each program in three fresh Node
// processes and once more in a process that has run another program of the
// same seed (plan.ts). Each mutant of #37's table must fail its property
// within that budget. Runs on Node: `node --test conformance/`.

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
      const most = Math.max(...outcome.results.map((run) => run.maxOps));
      context.diagnostic(`${outcome.results.length} runs reported, ` +
        `most operations in one task ${most}, wall time ${seconds} s`);
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
      assert.notEqual(violation, undefined, `${mutant} passed ${property}`);
      if (violation !== undefined) {
        context.diagnostic(await evidence(violation, mutant));
      }
    });
}
