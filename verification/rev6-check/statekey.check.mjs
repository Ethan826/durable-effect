// statekey.check.mjs: checks model.mjs's stateKey against its claim. Two
// states with equal keys, reached by different paths, must have identical
// futures. For every such merge it checks one step (same choices; for
// every choice, equal successor keys and the same new stream items). For
// a sample of merges whose subtrees fit a cap it checks the whole future:
// the stream suffixes of all terminal descendants, as multisets, must be
// equal. Exits non-zero on any failure.
// Usage: node statekey.check.mjs [nodeCap] [deepChecks] [subtreeCap]
//        [broken]
// With "broken", the key drops true time (trueTime, sampleTime and the
// times derived from it); the check must then fail, which shows it can.

import { createHash } from "node:crypto";
import * as M from "./model.mjs";

const [nodeCap, deepChecks, subtreeCap] = [
  Number(process.argv[2] ?? 40000),
  Number(process.argv[3] ?? 200),
  Number(process.argv[4] ?? 20000),
];

const broken = process.argv[5] === "broken";

// The key under test; the broken one drops fields a later step reads.
const keyOf = (state) => {
  if (!broken) return M.stateKey(state);
  const key = JSON.parse(M.stateKey(state));
  delete key.env.trueTime;
  delete key.env.sampleTime;
  if (key.env.cur) delete key.env.cur.lastExchange;
  if (key.exec) {
    delete key.exec.lastVisible;
    delete key.exec.abortTime;
  }
  return JSON.stringify(key);
};

const fiber = (id, body, daemon = false) => ({ id, daemon, body });
const PROGRAMS = {
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
  vi_freezeTwoRuns: [fiber("f0", [{ s: "run", op: "r1", behaviour: "ok" },
    { s: "run", op: "r2", behaviour: "retryable", deadline: 1 },
    { s: "await", op: "r1" }])],
};

// A seeded shuffle, so that a capped search reaches every kind of choice
// rather than only the endings, which come last in choices().
let seed = 20261124;
const random = (n) => {
  seed = (Math.imul(seed, 1103515245) + 12345) >>> 0;
  return (seed >>> 8) % n;
};
const shuffled = (list) => {
  const out = [...list];
  for (let i = out.length - 1; i > 0; i -= 1) {
    const j = random(i + 1);
    [out[i], out[j]] = [out[j], out[i]];
  }
  return out;
};

const hash = (value) =>
  createHash("sha1").update(JSON.stringify(value)).digest("base64");

const suffix = (state, from) => M.streamOf(state).slice(from);

// One step from each of two equal-key states must agree.
const oneStep = (a, b) => {
  const ca = M.choices(a);
  if (JSON.stringify(ca) !== JSON.stringify(M.choices(b))) return "choices";
  const la = M.streamOf(a).length;
  const lb = M.streamOf(b).length;
  for (const choice of ca) {
    const na = M.step(a, choice);
    const nb = M.step(b, choice);
    if (keyOf(na) !== keyOf(nb)) return `key after ${choice}`;
    if (hash(suffix(na, la)) !== hash(suffix(nb, lb))) {
      return `stream after ${choice}`;
    }
  }
  return null;
};

// The multiset of terminal stream suffixes below a state, or null if the
// subtree passes the cap.
const futures = (start) => {
  const from = M.streamOf(start).length;
  const counts = new Map();
  const stack = [start];
  let nodes = 0;
  while (stack.length > 0) {
    const state = stack.pop();
    nodes += 1;
    if (nodes > subtreeCap) return null;
    const choices = M.choices(state);
    if (choices.length === 0) {
      const h = hash(suffix(state, from));
      counts.set(h, (counts.get(h) ?? 0) + 1);
      continue;
    }
    for (const choice of choices) stack.push(M.step(state, choice));
  }
  return [...counts.entries()].sort().map((e) => e.join("*")).join(",");
};

const checkProgram = (name, fibers) => {
  const first = new Map();
  const row = { name, states: 0, keys: 0, merges: 0, oneStepFail: 0,
    deepPass: 0, deepFail: 0, deepSkipped: 0, firstFailure: null };
  const stack = [M.initial({ fibers })];
  let deepLeft = deepChecks;
  while (stack.length > 0 && row.states < nodeCap) {
    const state = stack.pop();
    row.states += 1;
    const key = keyOf(state);
    const seen = first.get(key);
    if (!seen) {
      first.set(key, state);
      for (const choice of shuffled(M.choices(state))) {
        stack.push(M.step(state, choice));
      }
      continue;
    }
    row.merges += 1;
    const bad = oneStep(seen, state);
    if (bad) {
      row.oneStepFail += 1;
      row.firstFailure ??= bad;
    }
    // Deep checks are spread over the search, one merge in eight.
    if (deepLeft <= 0 || random(8) !== 0) continue;
    const fa = futures(seen);
    const fb = fa === null ? null : futures(state);
    if (fa === null || fb === null) {
      row.deepSkipped += 1;
      continue;
    }
    deepLeft -= 1;
    if (fa === fb) row.deepPass += 1;
    else {
      row.deepFail += 1;
      row.firstFailure ??= "deep futures differ";
    }
  }
  row.keys = first.size;
  row.capped = stack.length > 0;
  return row;
};

let failed = false;
for (const [name, fibers] of Object.entries(PROGRAMS)) {
  const t0 = Date.now();
  const row = checkProgram(name, fibers);
  row.secs = (Date.now() - t0) / 1000;
  console.log(JSON.stringify(row));
  if (row.oneStepFail > 0 || row.deepFail > 0) failed = true;
}
if (broken) {
  console.log(failed ? "broken key rejected, as it must be"
    : "BROKEN KEY PASSED: the check cannot fail");
  process.exit(failed ? 0 : 1);
}
process.exit(failed ? 1 : 0);
