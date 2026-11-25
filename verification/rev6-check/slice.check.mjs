// slice.check.mjs: projection checks that justify checking one dimension
// of the schedule apart from the rest. For each program it enumerates
// every complete history under two settings, projects away the dimension,
// and requires the two sets of projected histories to be equal.
//   readings: readings {0, 2, 3} against {0}, projecting away every value
//     that carries a reading (sample.reading, clock.L, and each sample
//     notification's value wherever an entry appears).
//   ticks: ticks kept against none, with readings {0} on both sides,
//     projecting away sample.trueTime and the warnings. Only programs
//     with no run statement, the programs tier.mjs runs without ticks:
//     ticks are read only by R1's stall, which needs a run's closure.
// A program whose tree passes the leaf cap is retried with narrower
// limits (no ticks for the readings check, then one cancel, then one
// attempt); the narrowing used is reported. Exits non-zero if any
// program's sets differ.
// "readings-control" compares without the projection and must fail,
// which shows the check can. "ticks-control" runs the ticks comparison on
// the named programs that have a run, where ticks are observable, and
// must fail.
// Usage: node slice.check.mjs readings|ticks|readings-control|ticks-control
//        [leafCap] [randomCount]

import { createHash } from "node:crypto";
import * as M from "./model.mjs";

const which = process.argv[2] ?? "readings";
const leafCap = Number(process.argv[3] ?? 1500000);
const randomCount = Number(process.argv[4] ?? 20);

const fiber = (id, body, daemon = false) => ({ id, daemon, body });
const NAMED = {
  i_runAwait: [fiber("f0", [{ s: "run", op: "r1", behaviour: "ok" },
    { s: "await", op: "r1" }])],
  ii_sleep1Await: [fiber("f0", [{ s: "sleep", op: "s1", ms: 1 },
    { s: "await", op: "s1" }])],
  iii_runCallRace: [fiber("f0", [
    { s: "run", op: "r1", behaviour: "honour" },
    { s: "call", op: "c1", result: "ok" }, { s: "race", ops: ["r1", "c1"] }])],
  iv_forkDaemon: [fiber("f0", [{ s: "fork", fiber: "f1" }]),
    fiber("f1", [{ s: "run", op: "r1", behaviour: "ok" },
      { s: "await", op: "r1" }], true)],
  iv_forkDaemonRootWaits: [fiber("f0", [{ s: "fork", fiber: "f1" },
    { s: "sleep", op: "s1", ms: 0 }, { s: "await", op: "s1" }]),
  fiber("f1", [{ s: "run", op: "r1", behaviour: "ok" },
    { s: "await", op: "r1" }], true)],
  v_ensuringCall: [fiber("f0", [{ s: "sleep", op: "s1", ms: 1 },
    { s: "ensuring", body: [{ s: "await", op: "s1" }],
      finalizer: [{ s: "call", op: "c1", result: "ok" },
        { s: "await", op: "c1" }] }])],
  vii_sleepsAndClock: [fiber("f0", [{ s: "sleep", op: "s1", ms: 2 },
    { s: "sleep", op: "s2", ms: 1 }, { s: "await", op: "s1" },
    { s: "clock" }, { s: "await", op: "s2" }])],
  vi_freezeTwoRuns: [fiber("f0", [{ s: "run", op: "r1", behaviour: "ok" },
    { s: "run", op: "r2", behaviour: "retryable", deadline: 1 },
    { s: "await", op: "r1" }])],
};

const statementsOf = (stmts) => stmts.flatMap((s) =>
  [s, ...statementsOf(s.body ?? []), ...statementsOf(s.finalizer ?? [])]);
const hasRun = (fibers) => fibers
  .some((f) => statementsOf(f.body).some((s) => s.s === "run"));
const withoutRun = (fibers) => !hasRun(fibers);
const any = () => true;
const pick = (named, filter) => Object.fromEntries(
  Object.entries(named).filter(([, fibers]) => filter(fibers)));

// Twenty programs of three statements, picked with a fixed seed from those
// that pass the filter.
const randomPrograms = (filter) => {
  const all = [...M.programs({ fibers: 2, statements: 3, ops: 3 })]
    .filter((p) => filter(p.fibers));
  let seed = 3;
  const out = {};
  for (let k = 0; k < randomCount; k += 1) {
    seed = (Math.imul(seed, 1103515245) + 12345) >>> 0;
    out[`random${k}`] = all[(seed >>> 8) % all.length].fibers;
  }
  return out;
};

// ---- projections ----

const sampleCmds = (history) => {
  const last = history.attempts.at(-1);
  const journal = last ? last.journalOut : [];
  return new Set(journal.filter((e) => e.e === "cmd" &&
    e.cmd.c === "run" && e.cmd.op === "sample").map((e) => e.idx));
};

const dropSampleValue = (samples) => (entry) =>
  entry.e === "notif" && samples.has(entry.of)
    ? { ...entry, value: "<reading>" } : entry;

const readingEvent = (fix) => (event) => {
  if (event.t === "sample") return { ...event, reading: "<reading>" };
  if (event.t === "clock") return { ...event, L: "<L>" };
  if (event.t === "consume") return { ...event, entry: fix(event.entry) };
  return event;
};

const projectReadings = (history) => {
  const fix = dropSampleValue(sampleCmds(history));
  return { ...history, attempts: history.attempts.map((a) => ({
    ...a, journalIn: a.journalIn.map(fix), journalOut: a.journalOut.map(fix),
    trace: a.trace.map(readingEvent(fix)),
  })) };
};

// Warnings are removed; End.at is recounted over the remaining events.
const projectTicks = (history) => ({
  ...history,
  attempts: history.attempts.map((a) => {
    const keep = (e) => e.t !== "warn";
    const before = a.trace.slice(0, a.end.at + 1).filter(keep).length;
    const trace = a.trace.filter(keep).map((e) =>
      e.t === "sample" ? { ...e, trueTime: "<t>" } : e);
    return { ...a, trace, end: { ...a.end, at: before - 1 } };
  }),
});

const SETTINGS = {
  "readings-control": {
    project: (history) => history,
    sides: [{ readings: [0, 2, 3] }, { readings: [0] }],
    ladder: [{ ticks: 0, cancels: 1 }],
    programs: () => ({ ...NAMED, ...randomPrograms(any) }),
  },
  readings: {
    project: projectReadings,
    sides: [{ readings: [0, 2, 3] }, { readings: [0] }],
    ladder: [{}, { ticks: 0 }, { ticks: 0, cancels: 1 },
      { ticks: 0, cancels: 1, attempts: 1 }],
    programs: () => ({ ...NAMED, ...randomPrograms(any) }),
  },
  ticks: {
    project: projectTicks,
    sides: [{ readings: [0] }, { readings: [0], ticks: 0 }],
    ladder: [{}, { cancels: 1 }, { cancels: 1, attempts: 1 }],
    programs: () => ({ ...pick(NAMED, withoutRun),
      ...randomPrograms(withoutRun) }),
  },
};
SETTINGS["ticks-control"] = { ...SETTINGS.ticks,
  programs: () => pick(NAMED, hasRun) };

// ---- enumeration ----

const hash = (value) =>
  createHash("sha1").update(JSON.stringify(value)).digest("base64");

// The projected histories of every leaf, or null past the cap. With
// `wanted`, it returns the projected JSON of those hashes instead.
const enumerate = (program, limits, project, wanted) => {
  const set = new Set();
  const found = new Map();
  const stack = [M.initial(program, { limits })];
  let leaves = 0;
  while (stack.length > 0) {
    const state = stack.pop();
    const choices = M.choices(state);
    if (choices.length === 0) {
      leaves += 1;
      if (leaves > leafCap) return null;
      const projected = project(M.history(state));
      const h = hash(projected);
      set.add(h);
      if (wanted && wanted.has(h) && !found.has(h)) {
        found.set(h, JSON.stringify(projected));
      }
      continue;
    }
    for (const choice of choices) stack.push(M.step(state, choice));
  }
  return { set, leaves, found };
};

const smallest = (program, limits, project, hashes) => {
  const { found } = enumerate(program, limits, project, new Set(hashes));
  return [...found.values()].sort((a, b) => a.length - b.length)[0];
};

const compare = (name, fibers, setting) => {
  const program = { fibers };
  for (const narrow of setting.ladder) {
    const lim = setting.sides.map((side) =>
      ({ ...M.limits, ...side, ...narrow }));
    const a = enumerate(program, lim[0], setting.project);
    const b = a && enumerate(program, lim[1], setting.project);
    if (!a || !b) continue;
    const onlyA = [...a.set].filter((h) => !b.set.has(h));
    const onlyB = [...b.set].filter((h) => !a.set.has(h));
    const row = { name, narrowing: narrow, leaves: [a.leaves, b.leaves],
      distinct: [a.set.size, b.set.size], onlyFirst: onlyA.length,
      onlySecond: onlyB.length };
    if (onlyA.length > 0) {
      row.example = smallest(program, lim[0], setting.project, onlyA);
    } else if (onlyB.length > 0) {
      row.example = smallest(program, lim[1], setting.project, onlyB);
    }
    return row;
  }
  return { name, skipped: "over the leaf cap at every narrowing" };
};

const setting = SETTINGS[which];
let failed = false;
const programs = setting.programs();
for (const [name, fibers] of Object.entries(programs)) {
  const t0 = Date.now();
  const row = compare(name, fibers, setting);
  row.secs = (Date.now() - t0) / 1000;
  if (row.example) {
    failed = true;
    row.example = row.example.slice(0, 4000);
  }
  if (row.skipped) failed = true;
  console.log(JSON.stringify(row));
}
if (which.endsWith("-control")) {
  console.log(failed ? "control failed, as it must"
    : "CONTROL PASSED: the check cannot fail");
  process.exit(failed ? 0 : 1);
}
console.log(failed ? `${which}: FAILED` : `${which}: holds`);
process.exit(failed ? 1 : 0);
