// The fixtures of the register's rev6-cancel group (F12 to F16) and rev6-replay-checks group (F20).
// Each implements the register's pass criterion and its negative control (issue #48, comment
// 7119394545). drive.mjs owns the processes and the helpers.
import { setTimeout as sleep } from "node:timers/promises";
import * as d from "./lib.mjs";

const AT_ONCE_MS = 50;

// Prints how long the server took to journal each cancel notification after the request was sent.
const cancelLatency = (rows, sentLines) => {
  const sent = sentLines.map((l) => Number(l.match(/sent at (\d+)/)[1]));
  const journaled = d.signalNotifications(rows).map((r) => Date.parse(r.appended_at));
  console.log(`  cancel request to journaled cancel notification: ${journaled.map((t, i) => `${t - sent[i]} ms`).join(", ")}`);
};

// ---------- F12 cancelSet (A3) ----------
// Pass: one SendSignal (cancel, signal index 1) per call issued, in call order, the first commands
// after the cancel notification, and no mismatch on replay.
const cancelSetCheck = (rows, expectedTargets) => {
  const signals = d.sendSignalsOf(rows);
  const notice = d.signalNotifications(rows)[0]?.index ?? Infinity;
  const after = d.commands(rows).filter((r) => r.index > notice);
  const leading = after.slice(0, signals.length).every((r) => r.entry_type === "Command: SendSignal");
  return d.all([
    [JSON.stringify(signals.map((s) => s.target)) === JSON.stringify(expectedTargets), `SendSignal targets ${JSON.stringify(signals.map((s) => s.target))} vs expected ${JSON.stringify(expectedTargets)}`],
    [signals.every((s) => s.signal?.Index === 1), `signal ids ${JSON.stringify(signals.map((s) => s.signal))}`],
    [signals.length > 0 && leading, `SendSignals are the first ${signals.length} commands after the cancel notification at ${notice}`]
  ]);
};
const allCalls = (rows) => d.callsOf(rows).map((c) => c.id);
// The "pending calls only" checker: expects SendSignals only for calls not completed before the cancel.
const pendingCalls = (rows) => {
  const notice = d.signalNotifications(rows)[0]?.index ?? Infinity;
  return d.callsOf(rows).filter((c) => !(d.completionIndex(rows, c.result) < notice)).map((c) => c.id);
};
// Journal queries on an invocation with an open attempt block for seconds (see run-out.txt), so
// the fixtures time their cancels and kills from the handler's own events, not from the journal.
const runCancelSet = async (service, variant, restartSdk) => {
  console.log(`\n-- F12 cancelSet ${variant} (${service})`);
  const inv = await d.send(`${service}/cancelSet`);
  await d.waitEvent(inv, "c:start");
  await sleep(1000);
  await d.dump("F12", variant, "precancel", inv);
  const sent = await d.cancel(inv);
  console.log(`  cancel HTTP ${sent}`);
  if (restartSdk) {
    await d.waitEvent(inv, "comp-start");
    await sleep(1000);
    console.log(`  killing the SDK process at ${new Date().toISOString()}, during the 4 s compensation run`);
    await restartSdk();
    console.log(`  SDK process restarted`);
    await d.dump("F12", variant, "afterkill", inv);
  }
  await d.completed(inv, 40000);
  const rows = await d.dump("F12", variant, "final", inv);
  cancelLatency(rows, [sent]);
  await d.showStatus(inv);
  await d.showChildren(inv);
  d.showEvents(inv);
  console.log(`  attempts in SDK log ${d.attemptsOf(inv)}; comp action runs ${d.actionsOf(inv, "comp")}; mismatch lines ${d.mismatchLines(inv).length}`);
  return { inv, rows };
};
export const F12 = async ({ restartSdk }) => {
  for (const [service, variant, restart] of [["CxLive", "live", null], ["CxReplay", "replay", null], ["CxLive", "kill", restartSdk]]) {
    const { inv, rows } = await runCancelSet(service, variant, restart);
    const check = cancelSetCheck(rows, allCalls(rows));
    const noMismatch = d.mismatchLines(inv).length === 0;
    d.verdict(`F12-${variant}`, d.all([[check.ok, check.reason], [noMismatch, `mismatch lines ${d.mismatchLines(inv).length}`], [allCalls(rows).length === 3, "three calls"]]));
    d.control(`F12-${variant}-pendingOnly`, cancelSetCheck(rows, pendingCalls(rows)));
  }
  const { rows } = await runCancelSet("CxExplicit", "explicitCancellation", null);
  d.control("F12-explicitCancellation", cancelSetCheck(rows, allCalls(rows)));
};

// ---------- F13 childrenSurvive (A4, A24) ----------
const runCancelled = async (target, variant, fixture, step) => {
  console.log(`\n-- ${fixture} ${variant} (${target})`);
  const inv = await d.send(target);
  await d.waitEvent(inv, `${step}:start`);
  await sleep(1000);
  const sent = await d.cancel(inv);
  console.log(`  cancel HTTP ${sent}`);
  const status = await d.completed(inv);
  const rows = await d.dump(fixture, variant, "final", inv);
  cancelLatency(rows, [sent]);
  await d.showStatus(inv);
  await d.showChildren(inv);
  d.showEvents(inv);
  return { inv, rows, status };
};
const rejectedWith = (e, name, code) => e?.settled === "rejected" && e.error === name && e.code === code;
export const F13 = async () => {
  const { inv, rows, status } = await runCancelled("CxLive/childrenSurvive", "main", "F13", "k");
  await sleep(500);
  const ev = (step) => d.lastEvent(inv, step);
  const runCommands = rows.filter((r) => r.entry_type === "Command: Run" && r.name === "r").length;
  d.verdict("F13", d.all([
    [rejectedWith(ev("k"), "CancelledError", 409), `race rejected ${JSON.stringify(ev("k"))}`],
    [ev("reRun")?.value === "r-value", `re-raced run ${JSON.stringify(ev("reRun"))}`],
    [runCommands === 1 && d.actionsOf(inv, "r") === 1, `Run "r" commands ${runCommands}, action runs ${d.actionsOf(inv, "r")}`],
    [rejectedWith(ev("reCall"), "TerminalError", 409), `re-raced call ${JSON.stringify(ev("reCall"))} (A24: TerminalError 409, not CancelledError)`],
    [ev("reSleep")?.value === "slept", `re-raced sleep ${JSON.stringify(ev("reSleep"))}`],
    [d.attemptsOf(inv) === 1, `attempts ${d.attemptsOf(inv)}`],
    [status.completion_result === "success", `outcome ${status.completion_result}`]
  ]));
  // Controls: the property "a re-await resolves" must fail for the dead combinator and for a
  // single cancelled promise, which reject at once.
  const dead = await runCancelled("CxLive/deadCombinator", "deadCombinator", "F13", "k");
  const again = d.lastEvent(dead.inv, "kAgain");
  d.control("F13-deadCombinator", { ok: !(again?.settled === "rejected" && again.ms < AT_ONCE_MS), reason: `re-await of the rejected race ${JSON.stringify(again)}` });
  const single = await runCancelled("CxLive/singleCancelled", "singleCancelled", "F13", "single");
  const singleAgain = d.lastEvent(single.inv, "singleAgain");
  d.control("F13-singleCancelled", { ok: !(singleAgain?.settled === "rejected" && singleAgain.ms < AT_ONCE_MS), reason: `re-await of the cancelled sleep ${JSON.stringify(singleAgain)}` });
};

// ---------- F14 compensate (A6) ----------
export const F14 = async () => {
  for (const [service, variant] of [["CxLive", "live"], ["CxReplay", "replay"]]) {
    const { inv, rows, status } = await runCancelled(`${service}/compensate`, variant, "F14", "x");
    const ev = (step) => d.lastEvent(inv, step);
    const [before, refund] = d.callsOf(rows);
    const targets = d.sendSignalsOf(rows).map((s) => s.target);
    d.verdict(`F14-${variant}`, d.all([
      [rejectedWith(ev("x"), "CancelledError", 409), `pre-cancel race ${JSON.stringify(ev("x"))}`],
      [ev("refund")?.value === "fast:refund", `refund call ${JSON.stringify(ev("refund"))}`],
      [ev("compRun")?.value === "ran", `run ${JSON.stringify(ev("compRun"))}`],
      [ev("compSleep")?.value === "slept", `sleep ${JSON.stringify(ev("compSleep"))}`],
      [refund && !targets.includes(refund.id), `SendSignal targets ${JSON.stringify(targets)}, refund child ${refund?.id}`],
      [d.signalNotifications(rows).length === 1, `cancel notifications ${d.signalNotifications(rows).length}`],
      [status.completion_result === "success", `outcome ${status.completion_result}`],
      [d.mismatchLines(inv).length === 0, `mismatch lines ${d.mismatchLines(inv).length}, attempts ${d.attemptsOf(inv)}`]
    ]));
    // Control: "no SendSignal to the call" must fail for the call made before the cancel.
    d.control(`F14-${variant}-preCancelCall`, { ok: !targets.includes(before.id), reason: `pre-cancel call ${before.id}, SendSignal targets ${JSON.stringify(targets)}` });
  }
};

// ---------- F15 secondCancel (A7), pinned as observed ----------
// Pinned from the first observation (2026-11-24 UTC, server 1.8.1, SDK 1.18.4, protocol v7): the
// second cancel request is delivered as a second cancel signal; at the next await the SDK sends a
// SendSignal to the call made during compensation (y) and rejects that await with CancelledError.
const PINNED = {
  cancelNotifications: 2,
  sendSignalTargets: ["x", "y"],
  y: { settled: "rejected", error: "CancelledError", code: 409 },
  after: "resolved",
  outcome: "success",
  attempts: 1
};
const observeSecond = async (variant, second) => {
  console.log(`\n-- F15 secondCancel ${variant}`);
  const inv = await d.send("CxLive/secondCancel");
  await d.waitEvent(inv, "x:start");
  await sleep(1000);
  const sent = [await d.cancel(inv)];
  console.log(`  first cancel HTTP ${sent[0]}`);
  await d.waitEvent(inv, "y:start");
  await sleep(1500);
  if (second) sent.push(await d.cancel(inv));
  if (second) console.log(`  second cancel HTTP ${sent[1]}, during the 10 s compensation call`);
  const status = await d.completed(inv);
  const rows = await d.dump("F15", variant, "final", inv);
  cancelLatency(rows, sent);
  await d.showStatus(inv);
  await d.showChildren(inv);
  d.showEvents(inv);
  const calls = d.callsOf(rows);
  const y = d.lastEvent(inv, "y");
  return {
    cancelNotifications: d.signalNotifications(rows).length,
    sendSignalTargets: d.sendSignalsOf(rows).map((s) => (s.target === calls[0].id ? "x" : s.target === calls[1]?.id ? "y" : s.target)),
    y: y && { settled: y.settled, error: y.error, code: y.code, value: y.value },
    after: d.lastEvent(inv, "after")?.settled,
    outcome: status.completion_result,
    attempts: d.attemptsOf(inv)
  };
};
export const F15 = async () => {
  const twice = await observeSecond("twoCancels", true);
  console.log(`  OBSERVED twoCancels ${JSON.stringify(twice)}`);
  const pinned = PINNED ?? twice;
  const same = (o) => JSON.stringify(o) === JSON.stringify(pinned);
  d.verdict("F15", { ok: PINNED !== null && same(twice), reason: `${PINNED === null ? "nothing pinned yet; " : ""}observed ${JSON.stringify(twice)} vs pinned ${JSON.stringify(PINNED)}` });
  const once = await observeSecond("oneCancel", false);
  console.log(`  OBSERVED oneCancel ${JSON.stringify(once)}`);
  d.control("F15-oneCancel", { ok: same(once), reason: `one cancel ${JSON.stringify(once)}; matches the two-cancel pin: ${same(once)}` });
};

// ---------- F16 cancelAtAwait (A8) ----------
const runBusy = async (handler) => {
  console.log(`\n-- F16 ${handler}`);
  const inv = await d.send(`CxLive/${handler}`);
  await d.waitEvent(inv, "busy-start");
  await sleep(1500);
  const sent = await d.cancel(inv);
  console.log(`  cancel HTTP ${sent} during the busy turn`);
  const status = await d.completed(inv);
  await sleep(1000);
  const rows = await d.dump("F16", handler, "final", inv);
  cancelLatency(rows, [sent]);
  await d.showStatus(inv);
  d.showEvents(inv);
  console.log(`  action "act" runs ${d.actionsOf(inv, "act")}; Run commands ${rows.filter((r) => r.entry_type === "Command: Run").length}`);
  return { inv, rows, status };
};
const notRunAndRejected = (inv) => {
  const raced = d.lastEvent(inv, "raceR");
  return d.all([
    [d.actionsOf(inv, "act") === 0, `action runs ${d.actionsOf(inv, "act")}`],
    [rejectedWith(raced, "CancelledError", 409), `race ${JSON.stringify(raced)}`]
  ]);
};
export const F16 = async () => {
  const main = await runBusy("cancelAtAwait");
  d.verdict("F16", notRunAndRejected(main.inv));
  const root = await runBusy("rootNoAwait");
  d.verdict("F16-rootNoAwait", d.all([
    [root.status.completion_result === "success", `outcome ${root.status.completion_result} ${root.status.completion_failure ?? ""}`],
    [d.actionsOf(root.inv, "act") === 0, `action runs ${d.actionsOf(root.inv, "act")}`]
  ]));
  const empty = await runBusy("emptyRace");
  d.verdict("F16-emptyRace", d.all([
    [d.lastEvent(empty.inv, "empty")?.value === "timeout", `race([]) against a 1.5 s timer ${JSON.stringify(d.lastEvent(empty.inv, "empty"))}`],
    [rejectedWith(d.lastEvent(empty.inv, "observe"), "CancelledError", 409), `next real await ${JSON.stringify(d.lastEvent(empty.inv, "observe"))}`]
  ]));
  const first = await runBusy("raceFirst");
  console.log(`  raceFirst after-turn await ${JSON.stringify(d.lastEvent(first.inv, "after"))}`);
  d.control("F16-raceFirst", notRunAndRejected(first.inv));
};

// ---------- F20 mismatch matrix (A15, A16) ----------
const MATRIX = [
  ["CxMatrix", "callParam", true], ["CxMatrix", "runName", true], ["CxMatrix", "sleepDuration", false],
  ["CxMatrix", "swappedAwakeables", false], ["CxMatrix", "raceMembers", false], ["CxMatrix", "identical", false],
  ["codec/CxCodec", "callParam", false], ["codec/CxCodec", "identical", false]
];
const serviceName = (path) => path.replace("codec/", "");
export const F20 = async () => {
  console.log("\n-- F20 mismatch matrix");
  const started = [];
  for (const [path, handler, expectMismatch] of MATRIX) started.push({ service: serviceName(path), handler, expectMismatch, inv: await d.send(`${serviceName(path)}/${handler}`) });
  // Watch every invocation for 9 s and keep each status and failure code it shows.
  for (const c of started) c.seen = { statuses: new Set(), codes: new Set() };
  for (const deadline = Date.now() + 9000; Date.now() < deadline; await sleep(250)) {
    for (const c of started) {
      const s = await d.statusOf(c.inv);
      c.seen.statuses.add(s.status);
      if (s.last_failure_error_code != null) c.seen.codes.add(s.last_failure_error_code);
    }
  }
  for (const c of started) {
    const status = await d.statusOf(c.inv);
    const lines = d.mismatchLines(c.inv);
    const mismatch = c.seen.codes.has(570) || lines.length > 0;
    console.log(`  seen statuses ${[...c.seen.statuses].join(",")}; failure codes ${[...c.seen.codes].join(",") || "none"}`);
    console.log(`\n  ${c.service}/${c.handler} ${c.inv}`);
    console.log(`  status ${JSON.stringify(status)}`);
    for (const l of lines.slice(0, 2)) console.log(`  sdk mismatch: ${l.slice(0, 600)}`);
    console.log(`  attempts ${d.attemptsOf(c.inv)}; children ${(await d.childrenOf(c.inv)).length}`);
    if (status.status !== "completed") console.log(`  kill HTTP ${await d.killInvocation(c.inv)} (stops the retries)`);
    await d.dump("F20", `${c.service}-${c.handler}`, "final", c.inv);
    c.status = status;
    c.mismatch = mismatch;
    c.ok = mismatch === c.expectMismatch && (mismatch || status.completion_result === "success");
    const name = `F20-${c.service}-${c.handler}`;
    const reason = `mismatch ${mismatch} (expected ${c.expectMismatch}); SDK mismatch records ${lines.length}; failure codes seen ${[...c.seen.codes].join(",") || "none"}; status ${status.status} ${status.completion_result ?? ""}; attempts ${d.attemptsOf(c.inv)}`;
    if (c.service === "CxMatrix" && c.handler === "identical") d.control(`F20-identicalReplay-mismatches`, { ok: mismatch, reason });
    else d.verdict(name, { ok: c.ok, reason });
  }
  const param = started.find((c) => c.service === "CxMatrix" && c.handler === "callParam");
  const ident = started.find((c) => c.service === "CxMatrix" && c.handler === "identical");
  // A16: a mismatch is retried (onJournalMismatchErrors "retry"), not paused or failed; journals are
  // replayed (explicitRecovery false): the identical case's run and call happened once.
  d.verdict("F20-A16-defaults", d.all([
    [!param.seen.statuses.has("paused") && !param.seen.statuses.has("completed") && d.attemptsOf(param.inv) >= 3, `mismatching invocation statuses seen ${[...param.seen.statuses].join(",")}, attempts ${d.attemptsOf(param.inv)}`],
    [d.attemptsOf(ident.inv) >= 2 && d.actionsOf(ident.inv, "count") === 1, `identical case attempts ${d.attemptsOf(ident.inv)}, run action runs ${d.actionsOf(ident.inv, "count")}`],
    [(await d.childrenOf(ident.inv)).length === 1, `identical case child calls ${(await d.childrenOf(ident.inv)).length}`]
  ]));
};
