// Prints PASS or FAIL for each rev6-rerun fixture (R5, R6, issue #48)
// and for its control, which must fail on every control invocation.
// Arguments: requested SDK version, requested server version, and the
// server binary's own --version output.
import { loadRun, entriesOf, allOf, noneOf } from "./check-lib.mjs";
import { r5Holds, r5Evidence } from "./check-r5.mjs";
import { r6Holds, r6Evidence } from "./check-r6.mjs";

// [id, name, rule, predicate, main variants, control variants, evidence]
const fixtures = [
  ["R5", "reabortOnReplay", "rule 1 mitigation 2", r5Holds,
    ["main"], ["fresh"], r5Evidence],
  ["R6", "secondWarningAtInactivity", "rule 1 mitigation 3", r6Holds,
    ["main"], ["fromsend"], r6Evidence]
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

const of = (id, variants) => variants.flatMap((v) => entriesOf(run, id, v));
let failures = versionsOk ? 0 : 1;
for (const [id, name, rule, holds, mains, controls, evidence] of fixtures) {
  const main = of(id, mains);
  const control = of(id, controls);
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
