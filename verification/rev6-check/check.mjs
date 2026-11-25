// The step 7 gate (issue #48, comment 7144185705): explores every
// program and schedule within the published bounds through model.mjs,
// judges each history with predicates.mjs, and reports coverage. The
// model and the predicates are written separately and import nothing
// from each other; this file only joins them.
//
//   node check.mjs                 exhaustive run, then every mutant
//   node check.mjs --mutant NAME   one mutant only
//   node check.mjs --sampled N     the wider, sampled run with N histories
//   node check.mjs --pin           rewrite pinned.json (owner approval)
//
// Exits 1 unless every predicate holds, every mutant fails at least one
// predicate, every named boundary is reached, and the counts match
// pinned.json.
import { readFileSync, writeFileSync, existsSync } from "node:fs";
import { join } from "node:path";
import * as model from "./model.mjs";
import { predicates, pairPredicates, boundaries } from "./predicates.mjs";

const here = import.meta.dirname;
const exhaustive = { fibers: 2, statements: 5, ops: 3 };
const sampledBounds = { fibers: 3, statements: 8, ops: 4 };
const requiredBoundaries = [
  "end:output", "end:suspended", "end:ended", "end:crashed", "end:killed",
  "end:retry", "replay", "cancel:unwinding", "cancel:duringSample",
  "cancel:afterRootExit", "cancel:twice", "sleep:overlap", "sleep:chain",
  "run:retained", "run:unstartedRetained", "freeze", "closing:wait",
  "deadline:fired", "compensation:send", "race:loser", "uninterruptible"
];

const argValue = (name) => {
  const i = process.argv.indexOf(name);
  return i < 0 ? undefined : process.argv[i + 1];
};

// Depth-first over every choice path from one program's initial state.
function* histories(program, options) {
  const stack = [model.initial(program, options)];
  while (stack.length > 0) {
    const state = stack.pop();
    const next = model.choices(state);
    if (next.length === 0) { yield model.history(state); continue; }
    for (const choice of next) stack.push(model.step(state, choice));
  }
}

// A random walk to a terminal state, for the sampled run.
const randomHistory = (program, random) => {
  let state = model.initial(program, {});
  for (let next = model.choices(state); next.length > 0;
    next = model.choices(state)) {
    state = model.step(state, next[Math.floor(random() * next.length)]);
  }
  return model.history(state);
};

const newTally = () => ({
  programs: 0, histories: 0, failures: new Map(), boundaries: new Map()
});

const fail = (tally, id, history, verdict) => {
  const entry = tally.failures.get(id) ?? { count: 0, witness: null };
  entry.count += 1;
  entry.witness ??= { program: history.program, msg: verdict.msg,
    detail: verdict.detail };
  tally.failures.set(id, entry);
};

const judge = (tally, history, previous) => {
  tally.histories += 1;
  for (const p of predicates) {
    const verdict = p.check(history);
    if (verdict !== null) fail(tally, p.id, history, verdict);
  }
  if (previous !== null) {
    for (const p of pairPredicates) {
      const verdict = p.check(previous, history);
      if (verdict !== null) fail(tally, p.id, history, verdict);
    }
  }
  for (const tag of boundaries(history)) {
    tally.boundaries.set(tag, (tally.boundaries.get(tag) ?? 0) + 1);
  }
};

const explore = (options) => {
  const tally = newTally();
  for (const program of model.programs(exhaustive)) {
    tally.programs += 1;
    let previous = null;
    for (const history of histories(program, options)) {
      judge(tally, history, previous);
      previous = history;
    }
  }
  return tally;
};

// A small deterministic generator, so the sampled run is repeatable.
const mulberry32 = (seed) => () => {
  seed = (seed + 0x6d2b79f5) | 0;
  let t = Math.imul(seed ^ (seed >>> 15), 1 | seed);
  t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
  return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
};

const sample = (count) => {
  const tally = newTally();
  const random = mulberry32(48);
  const programs = [...model.programs(sampledBounds)];
  for (let i = 0; i < count; i += 1) {
    const program = programs[Math.floor(random() * programs.length)];
    judge(tally, randomHistory(program, random), null);
  }
  tally.programs = programs.length;
  return tally;
};

const report = (label, tally) => {
  console.log(`== ${label}: ${tally.programs} programs, ${tally.histories} histories`);
  for (const [id, { count, witness }] of tally.failures) {
    console.log(`  FAIL ${id} in ${count} histories; first: ${witness.msg}`);
    console.log(`    program ${JSON.stringify(witness.program)}`);
  }
};

const unreached = (tally) =>
  requiredBoundaries.filter((tag) => !tally.boundaries.has(tag));

const pinnedFile = join(here, "pinned.json");
const counts = (tally) => ({ programs: tally.programs, histories: tally.histories });

const checkPinned = (tally) => {
  if (process.argv.includes("--pin")) {
    writeFileSync(pinnedFile, JSON.stringify(counts(tally), null, 1) + "\n");
    console.log("pinned", JSON.stringify(counts(tally)));
    return true;
  }
  if (!existsSync(pinnedFile)) { console.log("NO PINNED COUNTS"); return false; }
  const pinned = JSON.parse(readFileSync(pinnedFile, "utf8"));
  const same = pinned.programs === tally.programs &&
    pinned.histories === tally.histories;
  console.log(same ? "counts match pinned.json"
    : `COUNTS DIFFER from pinned.json: ${JSON.stringify(pinned)}`);
  return same;
};

const runMutants = (names) => names.map((name) => {
  const tally = explore({ mutant: name });
  const caught = [...tally.failures.keys()];
  console.log(`  mutant ${name}: ${caught.length > 0
    ? `caught by ${caught.join(", ")}` : "NOT CAUGHT"}`);
  return caught.length > 0;
});

const main = () => {
  const only = argValue("--mutant");
  if (only !== undefined) return runMutants([only]).every(Boolean);
  const sampledCount = argValue("--sampled");
  if (sampledCount !== undefined) {
    const tally = sample(Number(sampledCount));
    report("sampled (not exhaustive)", tally);
    return tally.failures.size === 0;
  }
  const started = Date.now();
  const tally = explore({});
  report("exhaustive", tally);
  console.log("boundaries:", JSON.stringify(Object.fromEntries(tally.boundaries)));
  const missing = unreached(tally);
  if (missing.length > 0) console.log("UNREACHED BOUNDARIES:", missing.join(", "));
  console.log(`exhaustive run took ${Math.round((Date.now() - started) / 1000)} s`);
  const pinnedOk = checkPinned(tally);
  console.log("== mutants");
  const mutantsOk = runMutants(Object.keys(model.MUTANTS)).every(Boolean);
  return tally.failures.size === 0 && missing.length === 0 && pinnedOk && mutantsOk;
};

const ok = main();
console.log(ok ? "GATE PASSES" : "GATE FAILS");
process.exit(ok ? 0 : 1);
