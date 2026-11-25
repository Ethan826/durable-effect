// smoke.mjs: runs hand-picked programs along hand-picked schedules and
// prints their histories compactly. Not a check: it only shows that the
// model runs and lets a reader compare traces with part 1's rules.
// Usage: node smoke.mjs [scenario-name] [--json]

import * as M from "./model.mjs";

const fiber = (id, body, daemon = false) => ({ id, daemon, body });
const prog = (...fibers) => ({ fibers });

// The default policy makes progress: samples read 1 or 2, closures settle,
// results are acknowledged, then ids, completions and timers arrive.
const DEFAULT = [/^sample:\d+:[12]$/, /^settle:/, /^ack:/, /^id:/, /^done:/,
  /^fire:/, /^end$/];

const pick = (choices, patterns) => {
  for (const pattern of patterns) {
    const hit = choices.find((c) => pattern.test(c));
    if (hit) return hit;
  }
  return null;
};

// Each script item is a regex for a choice to take as soon as it is
// available; default steps are taken until it is.
const drive = (program, script, options = {}) => {
  let state = M.initial(program, options);
  const taken = [];
  const take = (choice) => {
    taken.push(choice);
    state = M.step(state, choice);
  };
  for (const item of script) {
    for (let guard = 0; guard < 60; guard += 1) {
      const choices = M.choices(state);
      const want = pick(choices, [item]);
      if (want) {
        take(want);
        break;
      }
      const fallback = pick(choices, DEFAULT);
      if (!fallback) throw new Error(`stuck before ${item}: ${choices}`);
      take(fallback);
    }
  }
  for (let guard = 0; guard < 200 && M.choices(state).length; guard += 1) {
    const choices = M.choices(state);
    take(pick(choices, DEFAULT) ?? choices[0]);
  }
  return { state, taken };
};

const show = (e) => {
  const rest = { ...e };
  delete rest.t;
  const body = Object.entries(rest)
    .map(([k, v]) => `${k}=${JSON.stringify(v)}`).join(" ");
  return `${e.t}${body ? " " + body : ""}`;
};

const entry = (e) => {
  if (e.e === "cmd") return `${e.idx}:${JSON.stringify(e.cmd)}`;
  const value = JSON.stringify(e.value);
  if (e.e === "notif") return `${e.idx}:notif(${e.of})=${value}`;
  if (e.e === "cancel") return `${e.idx}:CANCEL`;
  return `${e.idx}:OUTPUT ${JSON.stringify(e.outcome)}`;
};

const print = (name, { state, taken }, json) => {
  const h = M.history(state);
  if (json) return console.log(JSON.stringify(h));
  console.log(`\n=== ${name}`);
  console.log(`schedule: ${taken.join(" ")}`);
  for (const a of h.attempts) {
    console.log(`-- attempt ${a.n}: end ${JSON.stringify(a.end)}`);
    console.log(`   journal: ${a.journalOut.map(entry).join(" | ")}`);
    a.trace.forEach((e, i) => console.log(`   ${i}. ${show(e)}`));
    for (const eff of a.effects) {
      console.log(`   effect ${JSON.stringify(eff)}`);
    }
  }
  console.log(`outcome: ${JSON.stringify(h.outcome)}`);
  for (const c of h.children) console.log(`child ${JSON.stringify(c)}`);
};

const SCENARIOS = {
  plainRun: () => drive(prog(fiber("f0", [
    { s: "run", op: "r1", behaviour: "ok" }, { s: "await", op: "r1" },
    { s: "clock" }])), []),

  // Decision 3's shape: a buffered result and a cancel behind a sample.
  cancelBehindResult: () => drive(prog(fiber("f0", [
    { s: "sleep", op: "s1", ms: 1 }, { s: "sleep", op: "s2", ms: 1 },
    { s: "ensuring", body: [{ s: "await", op: "s1" }, { s: "await", op: "s2" }],
      finalizer: [{ s: "call", op: "c1", result: "ok" },
        { s: "await", op: "c1" }] }])),
  [/^fire:2$/, /^fire:3$/, /^cancel$/, /^sample:/, /^sample:/, /^sample:/,
    /^id:/, /^cancel$/]),

  // C18, M2: a retryable failure freezes; the sibling's success is
  // proposed first; the next attempt replays it.
  freezeAndReplay: () => drive(prog(fiber("f0", [
    { s: "run", op: "r1", behaviour: "ok" },
    { s: "run", op: "r2", behaviour: "retryable" },
    { s: "await", op: "r1" }, { s: "await", op: "r2" }])),
  [/^settle:3$/, /^settle:2$/, /^ack:2$/, /^end$/]),

  // §7.3: the deadline's completion is consumed first, the run is aborted;
  // the closure ignores the signal; ticks bring both warnings.
  deadlineAndWarnings: () => drive(prog(fiber("f0", [
    { s: "run", op: "r1", behaviour: "ignoreOk", deadline: 1 },
    { s: "await", op: "r1" }])),
  [/^fire:3$/, /^tick$/, /^tick$/, /^tick$/, /^settle:/]),

  // M1: the loser of a race is queued behind the winner and dropped.
  raceLoserQueued: () => drive(prog(fiber("f0", [
    { s: "sleep", op: "s1", ms: 1 }, { s: "sleep", op: "s2", ms: 2 },
    { s: "race", ops: ["s1", "s2"] }, { s: "draw" }])),
  [/^fire:2$/, /^fire:3$/]),

  // §7.6: a run aborted by a lost race; crash before it settles; on
  // replay the gate and the check refuse to start it.
  reabortOnReplay: () => drive(prog(fiber("f0", [
    { s: "run", op: "r1", behaviour: "ignoreOk" },
    { s: "sleep", op: "s1", ms: 1 }, { s: "race", ops: ["r1", "s1"] }])),
  [/^fire:3$/, /^sample:/, /^crash$/]),

  // §8, C13, §7.7: a daemon's call is cancelled at closing; closing waits
  // for the call's id before Output.
  closingCancelsDaemonCall: () => drive(prog(
    fiber("f0", [{ s: "fork", fiber: "f1" }, { s: "sleep", op: "s1", ms: 0 },
      { s: "await", op: "s1" }]),
    fiber("f1", [{ s: "call", op: "c1", result: "ok" },
      { s: "await", op: "c1" }], true)), [/^fire:/, /^sample:/]),

  // C30: a cancel consumed after the root's exit is absorbed.
  lateCancel: () => drive(prog(fiber("f0", [
    { s: "run", op: "r1", behaviour: "ok" }])), [/^cancel$/]),

  // The same as lateCancel under the mutant that reports 409.
  lateCancelMutant: () => drive(prog(fiber("f0", [
    { s: "run", op: "r1", behaviour: "ok" }])), [/^cancel$/],
  { mutant: "lateCancelReports409" }),

  // A kill during attached compensation (A40).
  killDuringCompensation: () => drive(prog(fiber("f0", [
    { s: "sleep", op: "s1", ms: 3 },
    { s: "ensuring", body: [{ s: "await", op: "s1" }],
      finalizer: [{ s: "call", op: "c1", result: "ok" },
        { s: "await", op: "c1" }] }])),
  [/^cancel$/, /^sample:/, /^id:/, /^kill$/]),
};

const [, , only, flag] = process.argv;
const json = flag === "--json" || only === "--json";
for (const [name, run] of Object.entries(SCENARIOS)) {
  if (only && only !== "--json" && only !== name) continue;
  print(name, run(), json);
}
