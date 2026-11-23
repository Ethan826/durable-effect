import assert from "node:assert/strict";
import { test } from "node:test";
import { makeAdapter } from "../src/adapter/Runtime.ts";
import { programsPerSeed, seeds } from "./plan.ts";
import { describe } from "./properties.ts";
import type { Violation } from "./properties.ts";
import { lifecycleMutants } from "./liferegistry.ts";
import type { LifecycleMutantName } from "./liferegistry.ts";
import type { Variant } from "./mutants.ts";
import {
  fullScanOf,
  lifecycleProperties,
  runLifecycle,
  scanMinimums,
  shortfall,
  zeroScans,
} from "./lifeplan.ts";
import type { LifeOutcome } from "./lifeplan.ts";

// Properties I3, I4, I5, I6 and I8 of #37, by the dossier's conformance
// suite: seeds 1 to 5, 1,000 programs each, run in this one process (the
// dossier asks for fresh processes only for I1 and I2). Each mutant of
// #37's table must fail its property on a property finding within that
// budget. Runs on Node: `node --test conformance/`.

const empty: LifeOutcome = { programs: 0, violations: {}, scans: zeroScans };

test("every scan minimum names its shortfall when its count is low", () => {
  const short = lifecycleProperties.map((property) =>
    shortfall(property, empty).length
  );
  const floors = lifecycleProperties.map((property) =>
    scanMinimums[property].length
  );
  assert.deepEqual(short, floors);
  assert.equal(fullScanOf(empty), false);
});

/** A variant whose first task throws, as a crashed run would. */
const throws: Variant = (program, seed, host) => {
  const inner = makeAdapter(program, seed, host);
  return {
    runTask: (task) => {
      if (task._tag === "StartRoot") throw new Error("crashed");
      inner.runTask(task);
    },
  };
};

test("a run that throws is a run finding, not a property finding",
  async () => {
    const outcome = await runLifecycle(throws, 0, 1);
    const causes = lifecycleProperties.map((property) =>
      outcome.violations[property]?.cause
    );
    assert.deepEqual(causes, ["run", "run", "run", "run", "run"]);
  });

/** The adapter's full budget, run once and shared by the five tests. */
let adapterRuns: Promise<LifeOutcome> | undefined;
const startedAt = performance.now();
const fullBudget = () =>
  adapterRuns ??= runLifecycle(makeAdapter, 0, programsPerSeed);

for (const property of lifecycleProperties) {
  test(`${property} holds for the adapter: seeds 1-5, 1,000 programs each`,
    async (context) => {
      const outcome = await fullBudget();
      const seconds = Math.round((performance.now() - startedAt) / 1000);
      context.diagnostic(`${outcome.programs} programs; scans ` +
        `${JSON.stringify(outcome.scans)}; wall time ${seconds} s`);
      assert.equal(outcome.programs, seeds.length * programsPerSeed);
      const violation = outcome.violations[property];
      assert.equal(violation, undefined, describe(violation));
      assert.deepEqual(shortfall(property, outcome), []);
    });
}

/** Programs per seed in one round of a mutant's run. */
const roundSize = 25;

/** Runs a mutant round by round until its property fails, or the budget. */
const firstViolation = async (
  mutant: LifecycleMutantName,
  from = 0,
): Promise<Violation | undefined> => {
  if (from >= programsPerSeed) return undefined;
  const to = Math.min(from + roundSize, programsPerSeed);
  const { property, make } = lifecycleMutants[mutant];
  const outcome = await runLifecycle(make, from, to, [property]);
  return outcome.violations[property] ?? firstViolation(mutant, to);
};

const mutantNames = Object.keys(lifecycleMutants).filter(
  (name): name is LifecycleMutantName => name in lifecycleMutants,
);

/**
 * The check a mutant must fail, where the review named it: the I3 check
 * after a resume, the interrupt-only comparison, and the mask branch.
 */
const expected: Partial<Record<LifecycleMutantName, RegExp>> = {
  actsOnResume: /an executor action after a foreign resume/,
  withoutWrapper: /interrupt-only run: foreign interrupts changed the trace/,
  recordsThenForwards:
    /interrupt-only run: foreign interrupts changed the trace/,
  maskAll: /unmasked await of token \d+ reported no release/,
};

for (const mutant of mutantNames) {
  const property = lifecycleMutants[mutant].property;
  test(`mutant ${mutant} fails ${property} within the budget`,
    async (context) => {
      const violation = await firstViolation(mutant);
      // Only a property finding counts: a crash says nothing about the
      // property.
      assert.equal(violation?.cause, "property", describe(violation) ||
        `${mutant} passed ${property}`);
      context.diagnostic(describe(violation));
      const pattern = expected[mutant];
      if (pattern) assert.match(violation?.detail ?? "", pattern);
    });
}
