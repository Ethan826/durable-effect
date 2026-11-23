import assert from "node:assert/strict";
import { test } from "node:test";
import {
  comparedEvery,
  fullScan,
  programsPerSeed,
  requiredProgram,
  seeds,
} from "./plan.ts";
import type { Outcome } from "./processes.ts";
import { check, programsCompared, properties } from "./properties.ts";
import type { Role, RunResult } from "./runs.ts";

// Fixtures for the checks of I1, I2, I7 and I9 and for the scan floor
// (gate-integrity): runs that keep a property pass it, and for each
// comparison a run that breaks only that one fails it with a named
// message. gate.check.ts runs this file against checkers with one
// comparison turned off, and each must fail.

const clean = (seed: number, index: number, role: Role): RunResult => ({
  seed, index, role, logHash: "a", furtherHash: "b",
  identities: [0, 1], maxOps: 1, maxLoop: 1, misregistered: 0,
  statementLoops: 1,
});

const roles: ReadonlyArray<Role> = ["fresh0", "fresh1", "fresh2", "after"];

/** The four reported runs of one program, with `change` made to `role`. */
const program = (
  seed: number,
  index: number,
  change: { readonly role: Role; readonly to: Partial<RunResult> } | undefined,
): ReadonlyArray<RunResult> =>
  roles.map((role) => ({
    ...clean(seed, index, role),
    ...(change?.role === role ? change.to : {}),
  }));

const outcomeOf = (results: ReadonlyArray<RunResult>): Outcome =>
  ({ results, failures: [] });

const broken = (role: Role, to: Partial<RunResult>) =>
  outcomeOf(program(1, 0, { role, to }));

test("runs that keep every property pass every check", () => {
  const found = properties.map((property) =>
    check(property, outcomeOf(program(1, 0, undefined)))
  );
  assert.deepEqual(found, [undefined, undefined, undefined, undefined]);
});

test("I1 catches a differing log, and differing further tasks", () => {
  const log = check("I1", broken("fresh1", { logHash: "x" }));
  assert.match(log?.detail ?? "", /^log differs$/);
  assert.equal(log?.cause, "property");
  const further = check("I1", broken("after", { furtherHash: "x" }));
  assert.match(further?.detail ?? "", /^further tasks differs$/);
});

test("I2 catches a paced run whose log differs", () => {
  const found = check("I2", broken("fresh2", { logHash: "x" }));
  assert.match(found?.detail ?? "", /^log differs$/);
  assert.equal(found?.cause, "property");
});

test("I1 and I2 each compare only their own runs", () => {
  assert.equal(check("I1", broken("fresh2", { logHash: "x" })), undefined);
  assert.equal(check("I2", broken("fresh1", { logHash: "x" })), undefined);
});

test("I7 catches a repeated id, and ids that differ between runs", () => {
  const repeated = check("I7", broken("fresh0", { identities: [3, 3] }));
  assert.match(repeated?.detail ?? "", /^an id is reused: 3,3$/);
  const differ = check("I7", broken("after", { identities: [0, 2] }));
  assert.match(differ?.detail ?? "", /^ids differ: 0,1 \/ 0,2$/);
});

/** I9's limits, as the dossier fixes them, and the message at each. */
const i9Limits = [
  ["maxLoop", 2049, "operations in one run loop"],
  ["misregistered", 0, "fibers registered late or with frames"],
  ["statementLoops", 24, "statement-fiber loops in a task"],
  ["maxOps", 3_790_848, "operations in one task"],
] as const;

for (const [measure, limit, what] of i9Limits) {
  test(`I9 allows ${measure} at ${limit} and catches ${limit + 1}`, () => {
    assert.equal(check("I9", broken("fresh1", { [measure]: limit })),
      undefined);
    const found = check("I9", broken("fresh1", { [measure]: limit + 1 }));
    assert.equal(found?.cause, "property");
    assert.equal(found?.detail, `${limit + 1} > ${limit} ${what}`);
  });
}

test("a run missing from a program is a run finding", () => {
  const present = program(1, 0, undefined).filter((run) =>
    run.role !== "after"
  );
  const found = properties.map((property) =>
    check(property, outcomeOf(present))?.cause
  );
  assert.deepEqual(found, ["run", "run", "run", "run"]);
});

test("programs compared counts the programs with every run needed", () => {
  const whole = [...program(1, 0, undefined), ...program(2, 0, undefined)];
  const counts = (results: ReadonlyArray<RunResult>) =>
    properties.map((property) =>
      programsCompared(property, outcomeOf(results))
    );
  assert.deepEqual(counts(whole), [2, 2, 2, 2]);
  assert.deepEqual(counts([]), [0, 0, 0, 0]);
  const noPaced = whole.filter((run) =>
    !(run.seed === 2 && run.role === "fresh2")
  );
  assert.deepEqual(counts(noPaced), [2, 1, 1, 1]);
});

/** Every run of the full budget, leaving out the runs `skip` names. */
const fullBudget = (skip: (seed: number, index: number) => boolean) =>
  seeds.flatMap((seed) =>
    Array.from({ length: programsPerSeed }, (_, index) => index)
      .flatMap((index) => skip(seed, index) ? [] : program(seed, index,
        undefined))
  );

test("the scan floor needs the full budget and the required program", () => {
  const everything = fullBudget(() => false);
  assert.equal(fullScan(outcomeOf(everything)), true);
  const without = fullBudget((seed, index) =>
    seed === requiredProgram.seed && index === requiredProgram.index
  );
  assert.equal(without.length, everything.length - roles.length);
  assert.equal(fullScan(outcomeOf(without)), false);
  const repeats = [...without, ...program(1, 0, undefined)];
  assert.ok(repeats.length >= everything.length);
  assert.equal(fullScan(outcomeOf(repeats)), false);
  assert.equal(fullScan(outcomeOf([])), false);
});

test("the comparison floor needs every program of the budget compared", () => {
  const every = seeds.length * programsPerSeed;
  const everything = outcomeOf(fullBudget(() => false));
  assert.equal(comparedEvery(programsCompared("I1", everything)), true);
  assert.equal(comparedEvery(every - 1), false);
  assert.equal(comparedEvery(every + 1), false);
});
