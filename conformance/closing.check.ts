import assert from "node:assert/strict";
import { test } from "node:test";
import { closingCases, closingSampled } from "./closing.ts";
import { lifecycleChecks } from "./lifecheck.ts";
import { lifecycleRunOf } from "./lifecycle.ts";
import { lifeMutants } from "./lifemutants.ts";
import { coqLog, i4Breach, i6Breach, i7Breach, i8Breach } from "./logprops.ts";

// I8's pinned cases (closing.ts) under the adapter and the scripted host:
// a fiber registers during closing while Effect has it masked, and I8,
// I6 and Runtime.v's log properties hold. The I8 mutant that leaves out
// such a fiber must fail on the case.

const cases = Object.entries(closingCases);

/** Each case, with the I8 mutant that leaves out its masked fiber. */
const omitting = [
  ["maskedDetached", closingCases.maskedDetached, lifeMutants.omitDetached],
  ["closingForEach", closingCases.closingForEach, lifeMutants.omitInternal],
] as const;

test("the pinned I8 cases are the two #37 names", () => {
  assert.deepEqual(cases.map(([name]) => name),
    ["maskedDetached", "closingForEach"]);
});

for (const [name, handler] of cases) {
  test(`pinned case ${name}: a masked fiber registers during closing, ` +
    "and I6, I8 and Runtime.v's log properties hold", async (context) => {
    const run = await lifecycleRunOf(handler, closingSampled, 0);
    const masked = run.registrations.filter((one) =>
      one.closing && one.masked
    );
    context.diagnostic(`registrations ${JSON.stringify(run.registrations)}`);
    assert.ok(masked.length > 0, "no masked registration during closing");
    const coq = coqLog(run.log);
    const found = [
      lifecycleChecks.I8(run), lifecycleChecks.I6(run),
      i4Breach(coq), i6Breach(coq), i7Breach(coq), i8Breach(coq),
    ];
    assert.deepEqual(found, Array.from({ length: 6 }, () => undefined));
  });
}

for (const [name, handler, make] of omitting) {
  test(`pinned case ${name} fails I8 without its masked fiber`,
    async (context) => {
      const run = await lifecycleRunOf(handler, closingSampled, 0, make);
      const breach = lifecycleChecks.I8(run);
      context.diagnostic(`${breach}`);
      assert.ok(breach !== undefined, "the mutant passed I8");
    });
}
