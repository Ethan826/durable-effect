// Prints PASS or FAIL for each rev6-runs fixture (R1 to R4, issue #48)
// and for its control, which must fail on every control invocation.
// Arguments: requested SDK version, requested server version, and the
// server binary's own --version output.
import { loadRun, allOf, noneOf } from "./check-lib.mjs";
import {
  entriesOf, r1Holds, r2Holds, r3Holds, r3sHolds, r1Evidence, r2Evidence, r3Evidence
} from "./check-runs.mjs";
import { r4Holds, r4Evidence } from "./check-abort.mjs";

// [id, name, rule, predicate, main variants, control variants, evidence]
const fixtures = [
  ["R1", "executingRunNeverDropped", "rule 1, A9", r1Holds,
    ["keep-live", "keep-replay"], ["drop-live", "drop-replay"], r1Evidence],
  ["R2", "closingWaitsForRuns", "rule 2, A21", r2Holds,
    ["wait-live", "wait-replay"], ["return-live", "return-replay"],
    r2Evidence],
  ["R3", "failureHeldUntilDelivered", "rule 3, A11", r3Holds,
    ["hold-live", "hold-replay"], ["nohold-live", "nohold-replay"],
    r3Evidence],
  ["R3s", "failureHeldUntilSettled (added after run 1)", "rule 3, A11",
    r3sHolds, ["settled-live", "settled-replay"],
    ["nohold-live", "nohold-replay"], r3Evidence],
  ["R4", "abortLoser", "abort signal", r4Holds,
    ["main"], ["noconvert", "noabort"], r4Evidence]
];

const [sdkWanted, serverWanted, serverReported] = process.argv.slice(2);
const run = loadRun();
const sdkLoaded = run.log.find((l) => l.startsWith("SDK_VERSION"))
  ?.split(" ")[1];
const versionsOk = sdkLoaded === sdkWanted &&
  serverReported === `restate-server ${serverWanted}`;
console.log(`VERSIONS ${versionsOk ? "PASS" : "FAIL"}: SDK requested ` +
  `${sdkWanted} loaded ${sdkLoaded}; server requested ${serverWanted} ` +
  `reports "${serverReported}"`);

const of = (variants) => variants.flatMap((v) => entriesOf(run, ...v));
let failures = versionsOk ? 0 : 1;
for (const [id, name, rule, holds, mains, controls, evidence] of fixtures) {
  const main = of(mains.map((v) => [id.slice(0, 2), v]));
  const control = of(controls.map((v) => [id.slice(0, 2), v]));
  const pass = allOf(main, (e) => holds(run, e));
  const controlFailed = noneOf(control, (e) => holds(run, e));
  if (!pass || !controlFailed) failures += 1;
  console.log(`${id} ${name} (${rule}): ${pass ? "PASS" : "FAIL"} on ` +
    `${main.length} invocations (${mains.join(", ")})`);
  console.log(`  control: ${controlFailed ? "FAILED as required" :
    "DID NOT FAIL (finding)"} on ${control.length} invocations ` +
    `(${controls.join(", ")})`);
  for (const line of evidence(run, [...main, ...control])) {
    console.log(`    ${line}`);
  }
}
console.log(`SUMMARY ${failures === 0 ? "all PASS" : `${failures} FAIL`}`);
process.exitCode = failures === 0 ? 0 : 1;
