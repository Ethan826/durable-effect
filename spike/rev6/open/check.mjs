// Judges the rev6-open fixtures (O1 to O3, issue #48 step 7) from
// out/manifest.json, out/sdk.log, out/effects.log and journals/. Prints
// one line per check and exits 1 unless every main variant passes and
// every control fails as required.
import {
  loadRun, entriesOf, journalOf, runResults, attemptsOf, eventsOf,
  effectCount, completedOk, allOf
} from "./check-lib.mjs";

const run = loadRun();
const [sdkVersion, serverVersion, serverBinary] = process.argv.slice(2);
console.log("versions: SDK", sdkVersion, "server", serverVersion, serverBinary);

let failures = 0;
const verdict = (label, ok, detail) => {
  if (!ok) failures += 1;
  console.log(ok ? "PASS" : "FAIL", label, detail);
};
const control = (label, failed, detail) => {
  if (!failed) failures += 1;
  console.log(failed ? "CONTROL-FAILS (as required)" : "CONTROL-PASSES (wrong)",
    label, detail);
};

// O1: the order of s1's completion, the cancel signal and s2's
// completion in the journal, as labels.
const sleepIds = (journal) => journal
  .filter((r) => r.entry.Command?.Sleep !== undefined)
  .map((r) => r.entry.Command.Sleep.completion_id);
const notifLabel = (ids) => (r) => {
  const n = r.entry.Notification;
  if (n === undefined) return null;
  if (n.ty === "Signal" && n.id.SignalIndex === 1) return "cancel";
  const position = ids.indexOf(n.id.CompletionId);
  return n.ty?.Completion === "Sleep" && position >= 0 ? `s${position + 1}` : null;
};
const journalOrder = (journal) =>
  journal.map(notifLabel(sleepIds(journal))).filter((l) => l !== null);
const ticksByAttempt = (id) => {
  const ticks = eventsOf(run, id).filter((e) => e.label === "tick-o1");
  const byAttempt = new Map();
  for (const e of ticks) {
    byAttempt.set(e.attempt, [...(byAttempt.get(e.attempt) ?? []), e.detail]);
  }
  return [...byAttempt.values()];
};
const isPrefix = (xs, ys) => xs.every((x, i) => ys[i] === x);
const o1Holds = (expected) => (e) => {
  const order = journalOrder(journalOf(e.journals[0]));
  const attempts = ticksByAttempt(e.id);
  return order.length === 3 && order.join() === expected(order).join() &&
    attempts.length > 1 && attempts.every((ts) => isPrefix(ts, order)) &&
    attempts.at(-1).join() === order.join();
};
const o1 = entriesOf(run, "O1", "main");
const o1Reached = (e) => journalOrder(journalOf(e.journals[0])).includes("cancel");
verdict("O1 scenario reached (a cancel journaled in every invocation)",
  allOf(o1, o1Reached), "");
verdict("O1 cancel handled in journal order on every replay",
  allOf(o1, (e) => completedOk(e) && o1Holds((o) => o)(e)),
  o1.map((e) => `${journalOrder(journalOf(e.journals[0])).join(">")} attempts=${ticksByAttempt(e.id).length}`).join("; "));
// Checker mutant: a predicate expecting the cancel last must reject.
control("O1 checker mutant (expects s1, s2, cancel)",
  !allOf(o1, o1Holds(() => ["s1", "s2", "cancel"])), "");

// O2: r's work starts live once (attempt 1) with the gate; the replay
// starts it again without the gate.
const liveStarts = (id) => eventsOf(run, id)
  .filter((e) => e.label === "r-start" && e.detail === "live");
const replayedAborted = (id) => eventsOf(run, id)
  .some((e) => e.label === "r-start" && e.detail === "aborted" && e.attempt > 1);
const o2Detail = (e) => `${e.id} attempts=${attemptsOf(run, e.id).length} ` +
  `rEffects=${effectCount(run, e.id, "r")} live=${liveStarts(e.id).map((s) => s.attempt)} ` +
  `rResult=${runResults(journalOf(e.journals[0]), "r").map((x) => JSON.stringify(x.result)).join(",")}`;
const o2Scenario = (e) => attemptsOf(run, e.id).length >= 2 &&
  liveStarts(e.id).some((s) => s.attempt === 1);
const gate = entriesOf(run, "O2", "gate");
verdict("O2 entry gate: r's work runs once, and replay enters it aborted",
  allOf(gate, (e) => o2Scenario(e) && effectCount(run, e.id, "r") === 1 &&
    replayedAborted(e.id)), gate.map(o2Detail).join("; "));
const nogate = entriesOf(run, "O2", "nogate");
control("O2 without the gate (r's work runs again on replay)",
  allOf(nogate, (e) => o2Scenario(e) && effectCount(run, e.id, "r") >= 2),
  nogate.map(o2Detail).join("; "));

// O3: a's outcome journaled by the failing attempt, so a runs once.
const o3Detail = (e) => `${e.id} attempts=${attemptsOf(run, e.id).length} ` +
  `a=${effectCount(run, e.id, "a")} b=${effectCount(run, e.id, "b")} ` +
  `aResult=${runResults(journalOf(e.journals[0]), "a").map((x) => JSON.stringify(x.result)).join(",")}`;
const ranOnce = (e) => attemptsOf(run, e.id).length === 2 &&
  effectCount(run, e.id, "a") === 1 && effectCount(run, e.id, "b") === 2;
const ranAgain = (e) => effectCount(run, e.id, "a") >= 2;
for (const [variant, kind] of [["okFreeze", "main"], ["termFreeze", "main"],
  ["okNoFreeze", "control"], ["termRetryableFirst", "control"]]) {
  const entries = entriesOf(run, "O3", variant);
  const detail = entries.map(o3Detail).join("; ");
  if (kind === "main") {
    verdict(`O3 ${variant}: a's outcome proposed before b's failure ends attempt 1`,
      allOf(entries, ranOnce), detail);
  } else {
    control(`O3 ${variant}: a runs again`, allOf(entries, ranAgain), detail);
  }
}

console.log(failures === 0 ? "ALL AS REQUIRED" : `${failures} NOT AS REQUIRED`);
process.exit(failures === 0 ? 0 : 1);
