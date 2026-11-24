// The rev6-idem fixtures, groups G1 to G6 (A39 to A42 of the register on #48).
//
// Every PREDICT entry below is the pass criterion, written from the server source at v1.8.1
// (restatedev/restate 20efb1b) before the first run:
//   - an idempotency key maps to a deterministic invocation id: sha256 over scope, service,
//     object key, handler and key; not the caller, not the payload (types/src/identifiers.rs:367-430);
//   - a request whose id already exists attaches to it while it runs, or gets its stored result
//     once it has completed (worker state_machine/mod.rs:1145-1170); it never runs again;
//   - a cancel of a running invocation only appends a cancel signal; the handler decides the
//     outcome, which is stored for the idempotency retention (lifecycle/cancel.rs:66-73, mod.rs:2866-2945);
//   - a cancel or kill of an inboxed or scheduled invocation answers its callers with 409 and,
//     because the experimental flag preflight_invocation_termination_retention is off by
//     default, frees the id (mod.rs:1827-1945, worker/src/partition/leadership/mod.rs:567-580);
//   - a kill under protocol >= 4 kills every Call and OneWayCall child in the journal
//     (mod.rs:2201-2260); a cancel or kill of a completed invocation answers AlreadyCompleted (409).
import { setTimeout as sleep } from "node:timers/promises";
import * as d from "./lib.mjs";

const RUN = Date.now().toString(36);
const key = (name) => `${name}-${RUN}`;

const PREDICT = {
  G1: {
    a: { first: "409", reissues: ["applied", "applied", "applied"], bodies: 1, applies: 1, ids: 1 },
    b: { first: "409", reissues: ["409", "409", "409"], bodies: 1, applies: 0, ids: 1 },
    c: { first: "409", reissues: ["409", "409", "409"], bodies: 1, applies: 0, ids: 1 },
    d: { first: "applied", cancelStatus: 409, reissues: ["applied", "applied", "applied"], bodies: 1, applies: 1, ids: 1 },
    expired: { first: "409", reissues: ["409", "409", "applied"], bodies: 2, applies: 1, ids: 1 }
  },
  G2: {
    a: { first: "409", reissues: ["applied", "applied", "applied"], bodies: 1, applies: 1, ids: 1 },
    b: { first: "409", reissues: ["409", "409", "409"], bodies: 1, applies: 0, ids: 1 },
    c: { first: "409", reissues: ["409", "409", "409"], bodies: 1, applies: 0, ids: 1 },
    d: { first: "applied", cancelStatus: 409, reissues: ["applied", "applied", "applied"], bodies: 1, applies: 1, ids: 1 },
    crossCaller: { status: "409", sameId: true, bodies: 1 }
  },
  G3: {
    sameKey: { y: "CancelledError", re: "409", re2: "409", bodies: 1, applies: 0, rows: 1, signalToChild: true },
    freshKey: { y: "CancelledError", re: "applied", re2: "applied", bodies: 2, applies: 1, rows: 2, signalToChild: true },
    objectSameKey: { y: "CancelledError", re: "applied", re2: "applied", bodies: 1, applies: 1, rows: 1, signalToChild: true },
    sendAttach: { y: "CancelledError", re: "applied", bodies: 1, applies: 1, rows: 1, signalToChild: false }
  },
  G4: { parent: "killed", child: "killed", grandchild: "killed", send: "killed", c0: "success", newCommandsAfterKill: 0, reissue: "409" },
  G5: { completedCancel: 409, completedKill: 409, unchanged: true, reissue: "applied", expiredCancel: 404 },
  G6: { notifications: 3, signals: ["y1", "y2"], y1: "CancelledError", y2: "CancelledError", after: "resolved", outcome: "success" }
};

// ---------- small helpers ----------
const labelEvent = (label, step) => d.sdkLines().find((l) => l.startsWith("EVENT ") && l.includes(`"step":"${step}"`) && l.includes(`"label":"${label}"`));
const waitLabel = (label, step, ms = 30000) => d.until(() => labelEvent(label, step), ms, `${label} ${step}`);
const waitRow = (k, status, ms = 30000) => d.until(async () => (await d.byKey(k)).find((r) => !status || r.status === status), ms, `${k} ${status}`);
const kindOfHttp = (r) => (r.status === 200 ? "applied" : String(r.status));
const kindOfSettle = (o) => (o?.settled === "resolved" ? "applied" : o?.error === "CancelledError" ? "CancelledError" : String(o?.code));
const sameList = (a, b) => JSON.stringify(a) === JSON.stringify(b);
const sendParent = (handler, body) => d.send(`IdParent/${handler}`, body);
const holdObject = (objectKey, ms) => d.send(`IdObject/${objectKey}/hold`, ms);
const at = (t0, ms) => sleep(Math.max(0, t0 + ms - Date.now()));
const parentEvent = (inv, step) => d.waitEvent(inv, step, 60000);
const counts = (label) => ({ bodies: d.bodiesOf(label).length, applies: d.appliesOf(label).length, ids: d.bodyInvocations(label).length });

// ---------- G1 and G2: A39 matrix ----------
// Each case: a first caller with key K, a cancel at the case's point, then three reissues with K
// at 0 ms, 3 s and 10 s after the cancel was sent.
const CASES = {
  a: { arg: (l) => ({ label: l }), object: true },
  b: { arg: (l) => ({ label: l, busyMs: 6000 }) },
  c: { arg: (l) => ({ label: l, preSteps: 2, holdMs: 30000 }) },
  d: { arg: (l) => ({ label: l, preSteps: 1 }) }
};
const DELAYS = [0, 3000, 10000];
const cancelPoint = async (name, label, k, firstDone) => {
  if (name === "a") await waitRow(k, "pending");
  if (name === "b") await waitLabel(label, "body");
  if (name === "c") await waitLabel(label, "hold:start");
  if (name === "d") await firstDone();
  if (name === "b" || name === "c") await sleep(1000);
  return (await waitRow(k)).id;
};
// caller.first(k, arg) starts the first call and returns { done }; caller.reissue(k, arg) awaits one.
const ingressCaller = (path) => ({
  first: (k, arg) => {
    const p = d.ingressCall(path, arg, k);
    return { done: () => p, result: async () => kindOfHttp(await p), raw: p };
  },
  reissue: async (k, arg) => {
    const r = await d.ingressCall(path, arg, k);
    return { kind: kindOfHttp(r), raw: { status: r.status, body: r.body.slice(0, 160), id: r.id, ms: r.ms } };
  }
});
const parentCaller = (target) => {
  const call = async (k, arg) => {
    const inv = await sendParent("callWithKey", { target, key: k, arg });
    return { inv, done: () => parentEvent(inv, "call") };
  };
  return {
    first: (k, arg) => {
      const started = call(k, arg);
      const done = async () => (await started).done();
      return { done, result: async () => kindOfSettle(await done()), raw: started };
    },
    reissue: async (k, arg) => {
      const { inv, done } = await call(k, arg);
      const o = await done();
      return { kind: kindOfSettle(o), raw: { parent: inv, settled: o.settled, value: o.value, error: o.error, code: o.code, message: o.message } };
    }
  };
};
const runCase = async (group, name, caller, label, k, arg, delays = DELAYS, lateArg = arg) => {
  console.log(`\n-- ${group} case ${name} (key ${k}, label ${label})`);
  const first = caller.first(k, arg);
  const inv = await cancelPoint(name, label, k, first.done);
  const cancel = await d.adminTerminate(inv, "cancel");
  console.log(`  target invocation ${inv}; cancel HTTP ${cancel.status} ${cancel.body.slice(0, 160)}`);
  const reissues = [];
  for (const [i, ms] of delays.entries()) {
    await at(cancel.sentAt, ms);
    const r = await caller.reissue(k, i === delays.length - 1 ? lateArg : arg);
    console.log(`  reissue at +${ms} ms: ${r.kind} ${JSON.stringify(r.raw)}`);
    reissues.push(r.kind);
  }
  const firstKind = await first.result();
  console.log(`  first caller: ${firstKind}`);
  for (const row of await d.byKey(k)) console.log(`  row ${JSON.stringify(row)}`);
  await d.dumpQuiet(group, name, "target", inv);
  const c = counts(label);
  console.log(`  counter: bodies ${c.bodies}, apply runs ${c.applies}, distinct invocation ids ${c.ids}; pre steps ${d.appliesOf(label, "pre0").length + d.appliesOf(label, "pre1").length}`);
  return { first: firstKind, cancelStatus: cancel.status, reissues, ...c, inv };
};
const caseCheck = (want, got) => d.all([
  [got.first === want.first, `first ${got.first} (want ${want.first})`],
  [want.cancelStatus === undefined || got.cancelStatus === want.cancelStatus, `cancel HTTP ${got.cancelStatus}`],
  [sameList(got.reissues, want.reissues), `reissues ${got.reissues.join(",")} (want ${want.reissues.join(",")})`],
  [got.bodies === want.bodies, `bodies ${got.bodies} (want ${want.bodies})`],
  [got.applies === want.applies, `apply runs ${got.applies} (want ${want.applies})`],
  [got.ids === want.ids, `invocation ids ${got.ids} (want ${want.ids})`]
]);
// The negative control: a reissue with a different key must run the body again.
const noRerun = (label, before) => ({ ok: d.bodiesOf(label).length === before, reason: `bodies for ${label}: ${before} before, ${d.bodiesOf(label).length} after a reissue with a different key` });

export const G1 = async () => {
  for (const name of ["a", "b", "c", "d"]) {
    const label = `g1${name}-${RUN}`;
    const objectKey = `g1obj-${RUN}`;
    if (CASES[name].object) console.log(`  hold the object key: ${await holdObject(objectKey, 8000)}`);
    if (CASES[name].object) await sleep(500);
    const path = CASES[name].object ? `IdObject/${objectKey}/apply` : "IdTarget/apply";
    const got = await runCase("G1", name, ingressCaller(path), label, key(`g1${name}`), CASES[name].arg(label));
    d.verdict(`A39-G1-ingress-${name}`, caseCheck(PREDICT.G1[name], got));
    if (name === "c") {
      const before = d.bodiesOf(label).length;
      const r = await d.ingressCall("IdTarget/apply", { label, preSteps: 1 }, key("g1c-other"));
      console.log(`  different-key reissue: HTTP ${r.status} ${r.body.slice(0, 80)}`);
      d.control("A39-G1-differentKey", noRerun(label, before));
    }
  }
  const label = `g1e-${RUN}`;
  const got = await runCase("G1", "expired", ingressCaller("IdShort/apply"), label, key("g1e"),
    { label, preSteps: 1, holdMs: 30000 }, [0, 1500, 14000], { label, preSteps: 1 });
  d.verdict("A39-G1-ingress-afterRetention", caseCheck(PREDICT.G1.expired, got));
};

export const G2 = async () => {
  for (const name of ["a", "b", "c", "d"]) {
    const label = `g2${name}-${RUN}`;
    const objectKey = `g2obj-${RUN}`;
    if (CASES[name].object) console.log(`  hold the object key: ${await holdObject(objectKey, 8000)}`);
    if (CASES[name].object) await sleep(500);
    const target = CASES[name].object ? `IdObject:${objectKey}` : "IdTarget";
    const k = key(`g2${name}`);
    const got = await runCase("G2", name, parentCaller(target), label, k, CASES[name].arg(label));
    d.verdict(`A39-G2-handler-${name}`, caseCheck(PREDICT.G2[name], got));
    if (name !== "c") continue;
    const before = d.bodiesOf(label).length;
    const cross = await d.ingressCall("IdTarget/apply", CASES.c.arg(label), k);
    console.log(`  ingress request with the handler's key: HTTP ${cross.status} ${cross.body.slice(0, 120)} x-restate-id ${cross.id}`);
    const want = PREDICT.G2.crossCaller;
    d.verdict("A39-G2-crossCaller", d.all([
      [kindOfHttp(cross) === want.status, `status ${cross.status}`],
      [cross.id === got.inv, `x-restate-id ${cross.id} vs the handler's child ${got.inv}`],
      [d.bodiesOf(label).length === before, `bodies ${d.bodiesOf(label).length}`]
    ]));
    const other = await parentCaller("IdTarget").reissue(key("g2c-other"), CASES.c.arg(label));
    console.log(`  different-key reissue from a handler: ${other.kind}`);
    d.control("A39-G2-differentKey", noRerun(label, before));
  }
};

// ---------- G3: reissue inside the compensating parent after a second cancel (A7) ----------
const G3_VARIANTS = {
  sameKey: (l) => ({ variant: "call", target: "IdTarget", key: key("g3s"), reissueKey: key("g3s"), arg: { label: l, preSteps: 1, holdMs: 10000 }, gapMs: 3000 }),
  freshKey: (l) => ({ variant: "call", target: "IdTarget", key: key("g3f"), reissueKey: key("g3f-2"), arg: { label: l, preSteps: 1, holdMs: 10000 }, gapMs: 3000 }),
  objectSameKey: (l) => ({ variant: "call", target: `IdObject:g3obj-${RUN}`, key: key("g3o"), reissueKey: key("g3o"), arg: { label: l, preSteps: 1 }, gapMs: 3000 }),
  sendAttach: (l) => ({ variant: "sendAttach", target: "IdTarget", key: key("g3a"), reissueKey: key("g3a"), arg: { label: l, preSteps: 1, holdMs: 8000 }, gapMs: 3000 })
};
const runG3 = async (name) => {
  const label = `g3${name}-${RUN}`;
  const body = G3_VARIANTS[name](label);
  console.log(`\n-- G3 ${name} (key ${body.key}, reissue key ${body.reissueKey})`);
  if (name === "objectSameKey") console.log(`  hold the object key 14 s: ${await holdObject(`g3obj-${RUN}`, 14000)}`);
  const inv = await sendParent("compensate", body);
  await parentEvent(inv, "x:start");
  await sleep(1000);
  console.log(`  first cancel HTTP ${(await d.adminTerminate(inv, "cancel")).status}`);
  if (name === "objectSameKey") await parentEvent(inv, "y:start");
  else await waitLabel(label, "hold:start");
  await sleep(1500);
  console.log(`  second cancel HTTP ${(await d.adminTerminate(inv, "cancel")).status}`);
  const status = await d.completed(inv, 90000);
  const rows = await d.dumpQuiet("G3", name, "parent", inv);
  const ev = (s) => d.lastEvent(inv, s);
  for (const s of ["y", "re", "re2"]) if (ev(s)) console.log(`  ${s}: ${JSON.stringify(ev(s))}`);
  const children = await d.byKey(body.key);
  const all = [...children, ...(body.reissueKey !== body.key ? await d.byKey(body.reissueKey) : [])];
  for (const r of all) console.log(`  row ${JSON.stringify(r)}`);
  const signals = d.sendSignalsOf(rows).map((s) => s.target);
  console.log(`  SendSignal targets ${JSON.stringify(signals)}; cancel notifications ${d.signalNotifications(rows).length}; parent ${status.completion_result}`);
  const c = counts(label);
  console.log(`  counter: bodies ${c.bodies}, apply runs ${c.applies}, ids ${c.ids}`);
  return { y: kindOfSettle(ev("y")), re: kindOfSettle(ev("re")), re2: ev("re2") ? kindOfSettle(ev("re2")) : undefined, ...c, rows: all.length, signalToChild: children.some((r) => signals.includes(r.id)) };
};
const g3Check = (want, got) => d.all(Object.keys(want).map((k) => [got[k] === want[k], `${k} ${got[k]} (want ${want[k]})`]));
export const G3 = async () => {
  const seen = {};
  for (const name of Object.keys(G3_VARIANTS)) {
    seen[name] = await runG3(name);
    d.verdict(`A7-A39-G3-${name}`, g3Check(PREDICT.G3[name], seen[name]));
  }
  d.control("A39-G3-freshKeyUnderSameKeyCheck", g3Check(PREDICT.G3.sameKey, seen.freshKey));
};

// ---------- G4: kill during compensation (A40) ----------
const failureOf = (row) => (row?.completion_result === "success" ? "success" : /killed/.test(row?.completion_failure ?? "") ? "killed" : row ? `${row.status}:${row.completion_failure ?? ""}` : "missing");
const childrenRows = (inv) => d.query(`SELECT id, target, status, completion_result, completion_failure FROM sys_invocation WHERE invoked_by_id = '${inv}' ORDER BY created_at`);
const runG4 = async (prefix, verb) => {
  console.log(`\n-- G4 ${verb} during compensation (prefix ${prefix})`);
  const k = key(`${prefix}-K`);
  const inv = await sendParent("killDuring", { prefix, key: k });
  await parentEvent(inv, "x:start");
  await sleep(1000);
  console.log(`  first cancel HTTP ${(await d.adminTerminate(inv, "cancel")).status}`);
  await waitLabel(`${prefix}-call`, "leaf:start");
  await d.until(() => d.bodiesOf(`${prefix}-send`).length > 0 && d.bodiesOf(`${prefix}-call-leaf`).length > 0, 20000, "send and leaf bodies");
  await sleep(1000);
  const pre = await d.dumpQuiet("G4", verb, "before", inv);
  const sent = await d.adminTerminate(inv, verb);
  console.log(`  ${verb} HTTP ${sent.status} ${sent.body.slice(0, 120)}`);
  await sleep(23000);
  const post = await d.dumpQuiet("G4", verb, "after", inv);
  const parent = await d.invocationRow(inv);
  const kids = await childrenRows(inv);
  const child = (await d.byKey(k))[0];
  const grand = child ? (await childrenRows(child.id))[0] : undefined;
  for (const r of [parent, ...kids, grand]) console.log(`  row ${JSON.stringify(r)}`);
  if (child) await d.dumpQuiet("G4", verb, "child", child.id);
  const send = kids.find((r) => r.target.startsWith("IdLeaf"));
  const c0 = kids.find((r) => r.id !== child?.id && r.target.startsWith("IdTarget"));
  const newCommands = d.commands(post).length - d.commands(pre).length;
  for (const l of ["call", "call-leaf", "send"]) console.log(`  counter ${prefix}-${l}: bodies ${d.bodiesOf(`${prefix}-${l}`).length}, apply runs ${d.appliesOf(`${prefix}-${l}`).length}`);
  const before = d.bodiesOf(`${prefix}-call`).length;
  const re = await d.ingressCall("IdTarget/apply", { label: `${prefix}-call`, preSteps: 1 }, k);
  console.log(`  ingress reissue with the child's key: HTTP ${re.status} ${re.body.slice(0, 120)}; bodies ${before} -> ${d.bodiesOf(`${prefix}-call`).length}`);
  return { parent: failureOf(parent), child: failureOf(child), grandchild: failureOf(grand), send: failureOf(send), c0: failureOf(c0), newCommandsAfterKill: newCommands, reissue: kindOfHttp(re) };
};
const g4Main = (got) => {
  const want = PREDICT.G4;
  return d.all(["parent", "child", "grandchild", "c0", "newCommandsAfterKill", "reissue"].map((k) => [got[k] === want[k], `${k} ${got[k]} (want ${want[k]})`]));
};
export const G4 = async () => {
  const killed = await runG4("g4k", "kill");
  d.verdict("A40-kill", g4Main(killed));
  d.verdict("A40-kill-oneWaySend", { ok: killed.send === PREDICT.G4.send, reason: `one-way send child ${killed.send} (source predicts killed; the docs say sends are not killed)` });
  const cancelled = await runG4("g4c", "cancel");
  d.control("A40-cancelInsteadOfKill", g4Main(cancelled));
};

// ---------- G5: cancel after completion (A41) ----------
const snapshot = async (inv) => JSON.stringify({ row: await d.invocationRow(inv), journal: (await d.journal(inv)).map((r) => [r.index, r.entry_type, r.entry_lite_json]) });
export const G5 = async () => {
  console.log("\n-- G5 cancel and kill after completion");
  const label = `g5-${RUN}`;
  const k = key("g5");
  const first = await d.ingressCall("IdTarget/apply", { label, preSteps: 1 }, k);
  const inv = first.id;
  const before = await snapshot(inv);
  const cancel = await d.adminTerminate(inv, "cancel");
  const kill = await d.adminTerminate(inv, "kill");
  console.log(`  completed ${inv}: cancel HTTP ${cancel.status} ${cancel.body}; kill HTTP ${kill.status} ${kill.body}`);
  await sleep(1500);
  const after = await snapshot(inv);
  await d.dumpQuiet("G5", "completed", "after", inv);
  const re = await d.ingressCall("IdTarget/apply", { label, preSteps: 1 }, k);
  console.log(`  status row and journal unchanged: ${before === after}; reissue HTTP ${re.status} ${re.body}; bodies ${d.bodiesOf(label).length}`);
  const sLabel = `g5s-${RUN}`;
  const shortFirst = await d.ingressCall("IdShort/apply", { label: sLabel, preSteps: 1 }, key("g5s"));
  await sleep(12000);
  const expired = await d.adminTerminate(shortFirst.id, "cancel");
  console.log(`  IdShort ${shortFirst.id} 12 s after completion (retention 4 s): cancel HTTP ${expired.status} ${expired.body}; rows ${(await d.byKey(key("g5s"))).length}`);
  const want = PREDICT.G5;
  d.verdict("A41", d.all([
    [cancel.status === want.completedCancel, `cancel of completed ${cancel.status}`],
    [kill.status === want.completedKill, `kill of completed ${kill.status}`],
    [(before === after) === want.unchanged, `unchanged ${before === after}`],
    [kindOfHttp(re) === want.reissue && d.bodiesOf(label).length === 1, `reissue ${kindOfHttp(re)}, bodies ${d.bodiesOf(label).length}`],
    [expired.status === want.expiredCancel, `cancel after retention ${expired.status}`]
  ]));
  const runningLabel = `g5r-${RUN}`;
  const running = d.ingressCall("IdTarget/apply", { label: runningLabel, holdMs: 20000 }, key("g5r"));
  await waitLabel(runningLabel, "hold:start");
  const runningInv = (await d.byKey(key("g5r")))[0].id;
  const live = await d.adminTerminate(runningInv, "cancel");
  console.log(`  cancel of a running invocation: HTTP ${live.status}; its caller got HTTP ${(await running).status}`);
  d.control("A41-runningCancel", { ok: live.status === want.completedCancel, reason: `cancel of a running invocation HTTP ${live.status}` });
};

// ---------- G6: a third cancel (A42) ----------
const runG6 = async (prefix, third) => {
  console.log(`\n-- G6 ${third ? "three" : "two"} cancels (prefix ${prefix})`);
  const inv = await sendParent("threeCancels", { prefix });
  await parentEvent(inv, "x:start");
  await sleep(1000);
  const sent = [await d.adminTerminate(inv, "cancel")];
  await waitLabel(`${prefix}-y1`, "hold:start");
  await sleep(1500);
  sent.push(await d.adminTerminate(inv, "cancel"));
  await waitLabel(`${prefix}-y2`, "hold:start");
  await sleep(1500);
  if (third) sent.push(await d.adminTerminate(inv, "cancel"));
  console.log(`  cancels HTTP ${sent.map((s) => s.status).join(",")}`);
  const status = await d.completed(inv, 60000);
  const rows = await d.dumpQuiet("G6", third ? "three" : "two", "parent", inv);
  const calls = d.callsOf(rows);
  const names = { [calls[0]?.id]: "y1", [calls[1]?.id]: "y2" };
  const signals = d.sendSignalsOf(rows).map((s) => names[s.target] ?? s.target);
  const ev = (s) => d.lastEvent(inv, s);
  for (const s of ["y1", "y2", "after"]) console.log(`  ${s}: ${JSON.stringify(ev(s))}`);
  console.log(`  SendSignal targets ${JSON.stringify(signals)}; cancel notifications ${d.signalNotifications(rows).length}; attempts ${d.attemptsOf(inv)}`);
  return { notifications: d.signalNotifications(rows).length, signals, y1: kindOfSettle(ev("y1")), y2: kindOfSettle(ev("y2")), after: ev("after")?.settled, outcome: status.completion_result };
};
const g6Check = (got) => {
  const want = PREDICT.G6;
  return d.all(Object.keys(want).map((k) => [JSON.stringify(got[k]) === JSON.stringify(want[k]), `${k} ${JSON.stringify(got[k])} (want ${JSON.stringify(want[k])})`]));
};
export const G6 = async () => {
  d.verdict("A42", g6Check(await runG6("g6t", true)));
  d.control("A42-twoCancels", g6Check(await runG6("g6w", false)));
};

// ---------- G7: what the retention period means (added after the first G5 run) ----------
// The first run showed a completed invocation still answering 12 s after a 4 s retention. The
// source explains it: expired invocations are removed only by the cleaner, which scans every
// worker.cleanup-interval (default 1 h; first scan after 20 to 40 % of it), cleaner.rs:150-157 and
// 204-215, config/worker.rs:62-67, 277. So the default-config prediction below was written AFTER
// that observation and is labelled so. The short-interval prediction is the original one from
// before the first run (G1 "expired" and G5's 404), now with the cleaner made to run every 2 s by
// RESTATE_WORKER__CLEANUP_INTERVAL.
const SHORT_CLEANUP = Boolean(process.env.RESTATE_WORKER__CLEANUP_INTERVAL);
const PREDICT_G7 = SHORT_CLEANUP
  ? { reissues: ["409", "applied"], bodies: 2, ids: 1, completedCancel: 404 }
  : { reissues: ["409", "409"], bodies: 1, ids: 1, completedCancel: 409 };
export const G7 = async () => {
  console.log(`\n-- G7 retention with cleanup interval ${process.env.RESTATE_WORKER__CLEANUP_INTERVAL ?? "default (1h)"}; prediction ${SHORT_CLEANUP ? "stated before the first run" : "written after the first run (post hoc)"}`);
  const label = `g7-${RUN}`;
  const k = key("g7");
  const first = d.ingressCall("IdShort/apply", { label, preSteps: 1, holdMs: 30000 }, k);
  await waitLabel(label, "hold:start");
  await sleep(1000);
  const inv = (await d.byKey(k))[0].id;
  const cancel = await d.adminTerminate(inv, "cancel");
  console.log(`  cancel HTTP ${cancel.status}; first caller HTTP ${(await first).status}`);
  const reissues = [];
  for (const ms of [1500, 14000]) {
    await at(cancel.sentAt, ms);
    const r = await d.ingressCall("IdShort/apply", { label, preSteps: 1 }, k);
    console.log(`  reissue at +${ms} ms: HTTP ${r.status} ${r.body.slice(0, 100)} x-restate-id ${r.id}`);
    reissues.push(kindOfHttp(r));
  }
  for (const row of await d.byKey(k)) console.log(`  row ${JSON.stringify(row)}`);
  const c = counts(label);
  const doneLabel = `g7done-${RUN}`;
  const done = await d.ingressCall("IdShort/apply", { label: doneLabel }, key("g7done"));
  await sleep(12000);
  const late = await d.adminTerminate(done.id, "cancel");
  console.log(`  cancel 12 s after completion (retention 4 s): HTTP ${late.status} ${late.body}`);
  const want = PREDICT_G7;
  d.verdict(`A39-A41-G7-${SHORT_CLEANUP ? "shortCleanup" : "defaultCleanup-posthoc"}`, d.all([
    [sameList(reissues, want.reissues), `reissues ${reissues.join(",")} (want ${want.reissues.join(",")})`],
    [c.bodies === want.bodies && c.ids === want.ids, `bodies ${c.bodies}, ids ${c.ids} (want ${want.bodies}, ${want.ids})`],
    [late.status === want.completedCancel, `cancel after retention HTTP ${late.status} (want ${want.completedCancel})`]
  ]));
};

// ---------- G8: A43, compensation issued as attached sends survives repeated cancels ----------
// Pass criteria, written before the first run (decision of 2026-11-23 on #48, step 3):
//   attach: parent journal has 3 cancel signal notifications and no SendSignal at all (so none to
//   either child); each child's body ran once and its "apply" ran once; each compensation step
//   resolves with "applied:<label>" (re-attach ticks are recorded, not limited); the parent
//   handler absorbs the first cancel, finishes the compensation and its "after" run, and ends
//   with outcome "success".
//   control (same two steps as request-response calls): fails that check, and shows a SendSignal
//   to at least one child and at least one child with no applied effect.
//   kill (attach variant, cancel then kill during the attached compensation): parent "killed",
//   both children "killed" (A40), no apply for either, no new parent command after the kill.
const PREDICT_A43 = { notifications: 3, signalsAll: [], bodies: [1, 1], applies: [1, 1], finals: ["applied:c1", "applied:c2"], after: "resolved", outcome: "success", children: ["success", "success"] };
const PREDICT_A43_KILL = { parent: "killed", children: ["killed", "killed"], applies: [0, 0], newCommandsAfterKill: 0 };
const A43_HOLD_MS = 12000;
const runA43 = async (variant, prefix, verb) => {
  console.log(`\n-- G8 A43 ${variant}${verb ? ` then ${verb}` : " with three cancels"} (prefix ${prefix})`);
  const keys = [key(`${prefix}-k1`), key(`${prefix}-k2`)];
  const inv = await sendParent("attachThree", { prefix, variant, holdMs: A43_HOLD_MS, keys });
  await parentEvent(inv, "x:start");
  await sleep(1000);
  const sent = [await d.adminTerminate(inv, "cancel")];
  await waitLabel(`${prefix}-c1`, "hold:start");
  await waitLabel(`${prefix}-c2`, "hold:start");
  await sleep(1500);
  const pre = verb === "kill" ? await d.dumpQuiet("G8", `${variant}-kill`, "before", inv) : undefined;
  sent.push(await d.adminTerminate(inv, verb ?? "cancel"));
  if (!verb) {
    await sleep(3500);
    sent.push(await d.adminTerminate(inv, "cancel"));
  }
  console.log(`  requests HTTP ${sent.map((s) => s.status).join(",")} at ${sent.map((s) => s.sentAt).join(",")}`);
  if (verb) await sleep(A43_HOLD_MS + 3000);
  const status = verb ? undefined : await d.completed(inv, 90000);
  if (!verb) await sleep(2000);
  const rows = await d.dumpQuiet("G8", verb ? `${variant}-${verb}` : variant, "parent", inv);
  const kids = [];
  for (const k of keys) kids.push((await d.byKey(k))[0]);
  for (const [i, kid] of kids.entries()) if (kid) await d.dumpQuiet("G8", verb ? `${variant}-${verb}` : variant, `child${i + 1}`, kid.id);
  const parentRow = await d.invocationRow(inv);
  for (const r of [parentRow, ...kids]) console.log(`  row ${JSON.stringify(r)}`);
  const finals = [1, 2].map((i) => d.lastEvent(inv, `a${i}:final`));
  for (const f of finals) console.log(`  final ${JSON.stringify(f)}`);
  for (const e of d.events(inv).filter((x) => /#|:final/.test(x.step))) console.log(`  event ${JSON.stringify(e)}`);
  const signals = d.sendSignalsOf(rows);
  const kidIds = kids.map((k) => k?.id);
  const labels = [`${prefix}-c1`, `${prefix}-c2`];
  console.log(`  SendSignal targets ${JSON.stringify(signals.map((s) => s.target))}; to children ${signals.filter((s) => kidIds.includes(s.target)).length}; cancel notifications ${d.signalNotifications(rows).length}; ticks ${JSON.stringify(finals.map((f) => f?.ticks))}; attempts ${d.attemptsOf(inv)}`);
  for (const l of labels) console.log(`  counter ${l}: bodies ${d.bodiesOf(l).length}, apply runs ${d.appliesOf(l).length}`);
  const re = verb ? await d.ingressCall("IdTarget/apply", { label: labels[0] }, keys[0]) : undefined;
  if (re) console.log(`  ingress with child 1's key after ${verb}: HTTP ${re.status} ${re.body.slice(0, 100)}`);
  return {
    notifications: d.signalNotifications(rows).length, signalsAll: signals.map((s) => s.target), toChildren: signals.filter((s) => kidIds.includes(s.target)).length,
    bodies: labels.map((l) => d.bodiesOf(l).length), applies: labels.map((l) => d.appliesOf(l).length),
    finals: finals.map((f, i) => (f?.settled === "resolved" ? f.value.replace(`${prefix}-`, "") : `${f?.settled}:${f?.code}`)),
    after: d.lastEvent(inv, "after")?.settled, outcome: status?.completion_result, children: kids.map((k) => failureOf(k)),
    parent: failureOf(parentRow), newCommandsAfterKill: pre ? d.commands(rows).length - d.commands(pre).length : undefined
  };
};
const a43Check = (got) => d.all(Object.keys(PREDICT_A43).map((k) => [JSON.stringify(got[k]) === JSON.stringify(PREDICT_A43[k]), `${k} ${JSON.stringify(got[k])} (want ${JSON.stringify(PREDICT_A43[k])})`]));
const a43KillCheck = (got) => d.all(Object.keys(PREDICT_A43_KILL).map((k) => [JSON.stringify(got[k]) === JSON.stringify(PREDICT_A43_KILL[k]), `${k} ${JSON.stringify(got[k])} (want ${JSON.stringify(PREDICT_A43_KILL[k])})`]));
export const G8 = async () => {
  const attach = await runA43("attach", `a43a-${RUN}`);
  d.verdict("A43-attachThreeCancels", a43Check(attach));
  const calls = await runA43("call", `a43c-${RUN}`);
  d.control("A43-asRequestResponseCalls", a43Check(calls));
  d.verdict("A43-control-mechanism", d.all([
    [calls.toChildren >= 1, `SendSignal to children ${calls.toChildren} (want at least 1)`],
    [calls.applies.some((n) => n === 0), `applies ${JSON.stringify(calls.applies)} (want at least one 0)`]
  ]));
  const killed = await runA43("attach", `a43k-${RUN}`, "kill");
  d.verdict("A43-kill-pinned", a43KillCheck(killed));
};
