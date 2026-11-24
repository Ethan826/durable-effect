// Prints PASS or FAIL for each rev6-order and rev6-effects fixture
// (register on #48) and for its negative control, which must fail.
// Arguments: requested SDK version, requested server version, and the
// server binary's own --version output.
import { loadRun } from "./check-lib.mjs";
import { checkF1, checkF2, checkF3, checkF4 } from "./check-order.mjs";
import { checkF9, checkF10, checkF11 } from "./check-sequence.mjs";
import { checkF5, checkF6, checkF7, checkF8 } from "./check-flow.mjs";
import { checkF17, checkF18, checkF19 } from "./check-effects.mjs";

const fixtures = [
  ["F1", "adjacentReplay", "A1", checkF1],
  ["F2", "subsetThenRace", "A2", checkF2],
  ["F3", "replacedRace (must-fail gate)", "A12", checkF3],
  ["F4", "turnWithoutRace", "A14", checkF4],
  ["F5", "manyInFlight", "A19", checkF5],
  ["F6", "droppedFailures", "A20", checkF6],
  ["F7", "returnsMidRace", "A21", checkF7],
  ["F8", "commandsAtAwait", "A22", checkF8],
  ["F9", "tenRuns", "A18", checkF9],
  ["F10", "startOrder", "A23", checkF10],
  ["F11", "protocolVersion", "A17", checkF11],
  ["F17", "droppedRunAtSuspension", "A9", checkF17],
  ["F18", "runExecutesWhen", "A10", checkF18],
  ["F19", "concurrentRetryableFailure", "A11", checkF19]
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

// Runs one check; a thrown error is a FAIL of that fixture, not a crash.
const judge = (check) => {
  try {
    return check(run);
  } catch (error) {
    const reason = `checker error: ${error.message}`;
    return { pass: { ok: false, reason }, control: { ok: false, reason },
      evidence: [] };
  }
};

let failures = versionsOk ? 0 : 1;
for (const [id, name, entry, check] of fixtures) {
  const { pass, control, evidence } = judge(check);
  const controlFailed = !control.ok;
  if (!pass.ok || !controlFailed) failures += 1;
  console.log(`${id} ${name} (${entry}): ${pass.ok ? "PASS" : "FAIL"}` +
    ` - ${pass.reason}`);
  console.log(`  control: ${controlFailed ? "FAILED as required" :
    "DID NOT FAIL (finding)"} - ${control.reason}`);
  for (const line of evidence) console.log(`    ${line}`);
}
console.log(`SUMMARY ${failures === 0 ? "all PASS" : `${failures} FAIL`}`);
process.exitCode = failures === 0 ? 0 : 1;
