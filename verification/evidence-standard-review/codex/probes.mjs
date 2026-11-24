import assert from "node:assert/strict";
import { pathToFileURL } from "node:url";
import { resolve } from "node:path";

const root = process.argv[2] ?? process.cwd();
const checker = pathToFileURL(resolve(root, "spike/rev6/rerun/check-r6.mjs"));
const { r6Holds } = await import(checker.href);

// Fixed grammar: one completed invocation, one abort, a correct grace
// warning, on-time deliveries at 1500/2500/3500 and replay deliveries
// at 10019 for 7000/8000. Sweep integer second-warning timestamps from
// 0 through 10000 ms. The claimed policy arms it 3000 ms after the
// last received result (3500 ms) in this idealized trace.
const entry = {
  id: "probe",
  status: { status: "completed", completion_result: "success" }
};
const event = (label, time, detail = "", attempt = 1) =>
  `EV probe ${attempt} ${label} ${time} ${detail}`;
const log = [
  event("issued", 0), event("abort-point", 1000),
  event("WARN-grace", 2000, "i"),
  event("tick-p1500", 1500, "p1500"),
  event("tick-p2500", 2500, "p2500"),
  event("tick-p3500", 3500, "p3500"),
  event("i-settle", 10003, "ok"),
  event("tick-p7000", 10019, "p7000", 2),
  event("tick-p8000", 10019, "p8000", 2)
];
const accepted = [];
for (let time = 0; time <= 10000; time++) {
  const run = { log: [...log, event("WARN-inactivity", time, "i")] };
  if (r6Holds(run, entry)) accepted.push(time);
}
assert.equal(accepted[0], 3500);
assert.equal(accepted.at(-1), 7000);
assert.ok(accepted.includes(6500));
assert.equal(accepted.length, 3501);
console.log("R6 check accepts 3,501 of 10,001 timestamps, inclusive 3500–7000 ms.");
console.log("A warning at the last result's delivery passes, 3000 ms before the claimed deadline.");

// Fixed grammar: two attempts, one already-executed effect without a
// result in the first attempt and a replay that either repeats the work
// or re-aborts. The second attempt writes one result and either reports
// failure or returns success. Compare effect count against observability
// through terminal status.
const outcomes = [];
for (const secondAttemptRunsWork of [false, true]) {
  for (const fails of [false, true]) {
    const effects = 1 + Number(secondAttemptRunsWork);
    outcomes.push({ effects, records: 1, status: fails ? "failure" : "success" });
  }
}
assert.ok(outcomes.some(({ effects, records, status }) =>
  effects === 2 && records === 1 && status === "success"));
console.log("Replay grammar: 4 traces, including 2 effects, 1 record, terminal success.");
