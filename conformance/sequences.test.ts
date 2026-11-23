import assert from "node:assert/strict";
import { test } from "node:test";
import fc from "fast-check";
import { mutants } from "./mutants.ts";
import { lifeMutants } from "./lifemutants.ts";
import type { Variant } from "./mutants.ts";
import { programsPerSeed, seeds } from "./plan.ts";
import {
  drive,
  sequence,
  sequenceBreach,
  sequenceChecks,
} from "./sequences.ts";
import type { Sequence } from "./sequences.ts";
import { unusualIn } from "./strays.ts";
import type { Unusual } from "./strays.ts";
import { coqLog } from "./logprops.ts";

// Arbitrary task sequences against Runtime.v's I4, I6, I7 and I8, by the
// owner's decision of 2026-11-22: 1,000 sequences for each of the pinned
// fast-check seeds 1 to 5, tasks the executor never sends included. Each
// check mirrors a Runtime.v definition (logprops.ts) and reads only the
// log. Runs on Node: `node --test conformance/`.

/**
 * The scan minimums over the full budget: the tasks the executor never
 * sends that the sequences must have sent, and the awaits and root exits
 * the checks judged. Each is the count the full budget gave when it was
 * set (Task 12), rounded down to two significant figures. Measured:
 * second starts 10,840, stray deliveries 46,776, stale interrupts 10,018,
 * awaits 2,407, root exits 3,718.
 */
const unusualFloors: Unusual = {
  secondStarts: 10_000,
  strayDeliveries: 46_000,
  staleInterrupts: 10_000,
  awaits: 2400,
  rootExits: 3700,
};

/** Each count below its floor, described. */
const shortOf = (counts: Unusual) =>
  Object.entries(unusualFloors).flatMap(([name, floor]) => {
    const seen = Reflect.get(counts, name);
    return seen < floor ? [`${name} ${seen} < ${floor}`] : [];
  });

const noUnusual: Unusual = {
  secondStarts: 0, strayDeliveries: 0, staleInterrupts: 0, awaits: 0,
  rootExits: 0,
};

test("the scan minimum names every count below its floor", () => {
  assert.equal(shortOf(noUnusual).length, 5);
  assert.deepEqual(shortOf(unusualFloors), []);
});

const sum = (left: Unusual, right: Unusual): Unusual => ({
  secondStarts: left.secondStarts + right.secondStarts,
  strayDeliveries: left.strayDeliveries + right.strayDeliveries,
  staleInterrupts: left.staleInterrupts + right.staleInterrupts,
  awaits: left.awaits + right.awaits,
  rootExits: left.rootExits + right.rootExits,
});

/** One seed's 1,000 sequences under `make`; counts what they sent. */
const checkSeed = (
  seed: number,
  make: Variant | undefined,
  holds: (log: ReturnType<typeof drive>) => boolean,
  counts: { total: Unusual; runs: number },
) => fc.check(fc.property(sequence, (one: Sequence) => {
  const log = drive(one, make);
  counts.total = sum(counts.total, unusualIn(log));
  counts.runs += 1;
  return holds(log);
}), { seed, numRuns: programsPerSeed });


test("I4, I6, I7 and I8 hold over arbitrary task sequences: seeds 1-5, " +
  "1,000 each", (context) => {
  const counts = { total: noUnusual, runs: 0 };
  const startedAt = performance.now();
  const failures = seeds.flatMap((seed) => {
    const details = checkSeed(seed, undefined,
      (log) => sequenceBreach(log) === undefined, counts);
    return details.failed ? [`seed ${seed}: ${JSON.stringify(
      details.counterexample)}`] : [];
  });
  const seconds = Math.round((performance.now() - startedAt) / 1000);
  context.diagnostic(`${counts.runs} sequences; ` +
    `${JSON.stringify(counts.total)}; wall time ${seconds} s`);
  assert.deepEqual(failures, []);
  assert.ok(counts.runs >= seeds.length * programsPerSeed, `${counts.runs}`);
  assert.deepEqual(shortOf(counts.total), []);
});

/**
 * Runtime defects each check must catch on some sequence: one mutant
 * per property, from the lifecycle suite's and I7's registries.
 */
const caught: ReadonlyArray<readonly [keyof typeof sequenceChecks, string,
  Variant]> = [
  ["I4", "neverReleases", lifeMutants.neverReleases],
  ["I6", "exitBeforeCleanup", lifeMutants.exitBeforeCleanup],
  ["I7", "sameIdentity", mutants.sameIdentity.make],
  ["I8", "omitInternal", lifeMutants.omitInternal],
];

for (const [property, name, make] of caught) {
  test(`the ${property} sequence check catches ${name}`, (context) => {
    const check = sequenceChecks[property];
    const counts = { total: noUnusual, runs: 0 };
    const found = seeds.map((seed) => checkSeed(seed, make,
      (log) => check(coqLog(log)) === undefined, counts))
      .find((details) => details.failed);
    assert.ok(found !== undefined, `${name} passed ${property}`);
    const [shrunk] = found.counterexample ?? [];
    assert.ok(shrunk !== undefined, "no counterexample");
    const breach = check(coqLog(drive(shrunk, make)));
    assert.ok(breach !== undefined, "the counterexample did not re-fail");
    context.diagnostic(`${breach}; case ${JSON.stringify(shrunk)}`);
  });
}
