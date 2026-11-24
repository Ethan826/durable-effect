import assert from "node:assert/strict";
import { resolve } from "node:path";
import { pathToFileURL } from "node:url";

const moduleAt = (path) => pathToFileURL(resolve(path)).href;
const { checkF9 } = await import(moduleAt("spike/rev6/order/check-sequence.mjs"));
const { loadRun } = await import(moduleAt("spike/rev6/order/check-lib.mjs"));
const run = loadRun();
const original = checkF9(run);
assert.equal(original.pass.ok, true);
assert.equal(original.control.ok, false);

// Change two winners within one actual replay while keeping the
// manifest, journal, record counts and event positions unchanged.
const replay = run.manifest.find(({ fixture, variant }) =>
  fixture === "F9" && variant === "replay");
const first = run.log.findIndex((line) =>
  line.startsWith(`TICK ${replay.id} `) && line.includes(" tick0 "));
const attempt = run.log[first].split(" ")[2];
const second = run.log.findIndex((line) =>
  line.startsWith(`TICK ${replay.id} ${attempt} tick1 `));
assert.ok(first >= 0 && second > first);
const log = [...run.log];
const [firstValue, secondValue] = [first, second].map((i) =>
  log[i].split(" ").slice(4).join(" "));
assert.notEqual(firstValue, secondValue);
log[first] = log[first].replace(firstValue, secondValue);
log[second] = log[second].replace(secondValue, firstValue);
assert.equal(checkF9({ ...run, log }).pass.ok, false);
console.log("F9: saved baseline passes, built-in control fails, and swapped in-scope replay winners fail the main predicate.");

// Fixed grammar: one issued run, two histories with the same durable
// prefix, exactly one local deadline firing, no completion or marker.
// Both deterministic decisions over the prefix are enumerated.
const histories = [
  { journal: ["Run(r)"], earlierAbort: false },
  { journal: ["Run(r)"], earlierAbort: true }
];
assert.deepEqual(histories[0].journal, histories[1].journal);
for (const abortAtReplayStart of [false, true]) {
  assert.equal(histories.filter(({ earlierAbort }) =>
    earlierAbort !== abortAtReplayStart).length, 1);
}
console.log("Deadline: either replay decision is wrong in one of two histories sharing the same durable prefix.");

// Fixed grammar: two one-draw fibers and two distinct draws. Project
// the same global values onto both receiver permutations.
const firstTrace = [["a", 7], ["b", 8]];
const secondTrace = [["b", 7], ["a", 8]];
const values = (trace) => trace.map(([, value]) => value);
assert.deepEqual(values(firstTrace), values(secondTrace));
assert.notEqual(Object.fromEntries(firstTrace).a, Object.fromEntries(secondTrace).a);
console.log("Random: equal global draw lists can assign different values to the same fiber.");
