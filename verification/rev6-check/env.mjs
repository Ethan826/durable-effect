// env.mjs: the environment of the step 7 check (#48, comment 7144185705).
// Restate's journal and server, the SDK's VM, attempts and their endings,
// replay, child invocations, run closures and their effect log, ticks and
// true time. Written from the register (comment 7119394545 and A39 to A43)
// and the run-rule fixtures (R1, R3, R6). It knows nothing of the executor's
// rules.
//
// Interface with the executor (rules.mjs). Nothing else crosses it.
//   The executor calls an `io` object built by makeIo(env, push):
//     io.issue(cmd) -> idx          the executor issues a command; live it is
//                                   appended, on replay it is matched against
//                                   the journal (a mismatch ends the attempt)
//     io.enterClosure(idx)          the wrapper calls the run's closure
//     io.refuseClosure(idx)         the wrapper refuses to call it
//     io.abortSignal(idx)           the executor aborts the run's signal
//     io.returnResult(idx, value)   the wrapper returns {ok}|{terminal}
//     io.returnRetryable(idx)       the wrapper returns a retryable failure
//     io.writeOutput(outcome)       Output; the attempt ends
//     io.failRetryable()            the handler failed retryably
//     io.emit(event)                append to the attempt's trace
//     io.now()                      the host clock in ticks (timers only)
//   The environment reports to the executor by pushing events, which
//   model.mjs dispatches:
//     { type: "consume", entry }    the awaited race resolved with entry
//     { type: "wrapper", idx }      the SDK asked for a run's closure (A10)
//     { type: "settled", idx, raw } a closure the wrapper entered settled;
//                                   raw is "ok" | "terminal" | "retryable" |
//                                   "interrupted" | "ownError" | {reading}
//   and model.mjs passes the executor's race members to the VM as keys:
//   "r:<cmdIdx>" for a completion and "i:<cmdIdx>" for an invocation id.

const INVOCATION_ID = "inv";

/** The key a notification resolves in a race. */
export const keyOf = (entry) =>
  entry.value && entry.value.invocationId !== undefined
    ? `i:${entry.of}`
    : `r:${entry.of}`;

const walkStatements = (stmts, visit) => {
  for (const stmt of stmts) {
    visit(stmt);
    if (stmt.body) walkStatements(stmt.body, visit);
    if (stmt.finalizer) walkStatements(stmt.finalizer, visit);
  }
};

const collectOps = (program) => {
  const ops = {};
  const record = (stmt) => {
    if (["run", "sleep", "call"].includes(stmt.s)) ops[stmt.op] = stmt;
  };
  for (const fiber of program.fibers) walkStatements(fiber.body, record);
  return ops;
};

/** A fresh environment for one invocation of `program`. */
export const newEnv = (program, limits) => ({
  limits,
  invocationId: INVOCATION_ID,
  opText: collectOps(program),
  journal: [],
  notified: {},
  trueTime: 0,
  ticks: 0,
  cancels: 0,
  done: [],
  cur: null,
  phase: "start",
  outcome: null,
  children: [],
  childOfCmd: {},
  childOfKey: {},
  sampleTime: {},
});

const indicesOf = (journal, test) =>
  journal.filter(test).map((entry) => entry.idx);

/** Start the next attempt; it replays the persisted journal (A18). */
export const beginAttempt = (env) => {
  const isArrival = (entry) => entry.e === "notif" || entry.e === "cancel";
  env.cur = {
    n: env.done.length,
    journalIn: structuredClone(env.journal),
    trace: [],
    effects: [],
    inbox: indicesOf(env.journal, isArrival),
    moved: 0,
    ready: [],
    a2: null,
    replay: indicesOf(env.journal, (entry) => entry.e === "cmd"),
    cursor: 0,
    sdkCalls: [],
    wrappers: {},
    signals: {},
    proposals: [],
    stalled: false,
    lastExchange: env.trueTime,
    ending: null,
    over: false,
  };
  env.phase = "attempt";
};

// ---- children (A24, A34, A39, A40, A41) ----

// AMBIGUOUS: a child's body is counted as run once when the server
// receives the call or send, even if a cancel or kill ends it first.
const newChild = (env, idx, kind, key) => {
  const child = {
    key, viaCmd: idx, attempt: env.cur.n, kind, ran: 1,
    cancelled: false, killed: false, status: "running", value: null,
    result: env.opText[env.journal[idx].cmd.op].result,
  };
  env.children.push(child);
  return env.children.length - 1;
};

// A39: a send's child is identified by its key, so a second send with the
// key attaches to the first child and runs nothing.
const childForSend = (env, idx, key) => {
  if (env.childOfKey[key] === undefined) {
    env.childOfKey[key] = newChild(env, idx, "send", key);
  }
  return env.childOfKey[key];
};

// A34, A41: a cancel ends a running child with 409; a completed child is
// unchanged.
const cancelChild = (env, target) => {
  const child = env.children[env.childOfCmd[target]];
  if (!child || child.status !== "running") return;
  child.cancelled = true;
  child.status = "done";
  child.value = { terminal: "409" };
};

const serverReceives = (env, cmd, idx) => {
  if (cmd.c === "call") env.childOfCmd[idx] = newChild(env, idx, "call", null);
  if (cmd.c === "send") env.childOfCmd[idx] = childForSend(env, idx, cmd.key);
  if (cmd.c === "attach") env.childOfCmd[idx] = env.childOfKey[cmd.target];
  if (cmd.c === "cancelCall") cancelChild(env, cmd.target);
};

const finishChild = (child) => {
  if (child.status === "running") {
    child.status = "done";
    child.value = child.result === "ok"
      ? { ok: "ok" }
      : { terminal: "error" };
  }
  return child.value;
};

// ---- commands and replay (S2, A15, A22) ----

const sameCmd = (left, right) =>
  JSON.stringify(left) === JSON.stringify(right);

const mismatch = (env) => {
  env.cur.mismatch = true;
  endAttempt(env, "crashed");
};

// A3: the VM tracks every call (not sends, A25) for its own cancels.
const trackCall = (cur, cmd, idx) => {
  if (cmd.c === "call") cur.sdkCalls.push(idx);
};

const replayCommand = (env, cmd) => {
  const cur = env.cur;
  const idx = cur.replay[cur.cursor];
  cur.cursor += 1;
  if (!sameCmd(env.journal[idx].cmd, cmd)) {
    mismatch(env);
    return -1;
  }
  trackCall(cur, cmd, idx);
  return idx;
};

const appendCommand = (env, cmd) => {
  const idx = env.journal.length;
  env.journal.push({ e: "cmd", idx, cmd });
  trackCall(env.cur, cmd, idx);
  serverReceives(env, cmd, idx);
  return idx;
};

const issue = (env, cmd) => {
  const cur = env.cur;
  if (!cur || cur.over) return -1;
  cur.lastExchange = env.trueTime;
  return cur.cursor < cur.replay.length
    ? replayCommand(env, cmd)
    : appendCommand(env, cmd);
};

// ---- arrivals (A17, A18, A33, R1) ----

// R1: once stalled, the server delivers nothing more to the attempt; the
// entry is journaled and reaches the next attempt through replay.
const deliver = (env, idx) => {
  const cur = env.cur;
  if (!cur || cur.over || cur.stalled) return;
  cur.inbox.push(idx);
  cur.lastExchange = env.trueTime;
};

const appendEntry = (env, entry) => {
  const idx = env.journal.length;
  env.journal.push({ ...entry, idx });
  if (entry.e === "notif") env.notified[keyOf({ ...entry, idx })] = true;
  deliver(env, idx);
  return idx;
};

const appendNotif = (env, of, value) =>
  appendEntry(env, { e: "notif", of, value });

const childIdValue = (env, idx) => ({
  invocationId: `child:${env.childOfCmd[idx]}`,
});

/** Every server-side completion that may be journaled now, as choices.
 * AMBIGUOUS: a timer may fire at any time after its command, whatever
 * the true time; P5's early-fire hypothesis is left to the predicate. */
export const arrivalChoices = (env) => {
  const out = [];
  const has = (key) => env.notified[key] === true;
  for (const entry of env.journal) {
    if (entry.e !== "cmd") continue;
    const { c } = entry.cmd;
    const i = entry.idx;
    if (c === "sleep" && !has(`r:${i}`)) out.push(`fire:${i}`);
    if ((c === "call" || c === "send") && !has(`i:${i}`)) out.push(`id:${i}`);
    const resultDue = c === "attach" || (c === "call" && has(`i:${i}`));
    if (resultDue && !has(`r:${i}`)) out.push(`done:${i}`);
  }
  return out;
};

/** Journal one server-side completion chosen by arrivalChoices. */
export const applyArrival = (env, kind, idx) => {
  if (kind === "fire") return appendNotif(env, idx, { ok: null });
  if (kind === "id") return appendNotif(env, idx, childIdValue(env, idx));
  const child = env.children[env.childOfCmd[idx]];
  return appendNotif(env, idx, finishChild(child));
};

/** A cancel request reaches Restate: a fresh signal each time (A42). */
export const appendCancel = (env) => {
  env.cancels += 1;
  appendEntry(env, { e: "cancel" });
};

// ---- the VM (A1, A2, A3, A4, A8, A10, A42) ----

// A3, A42: at the await that observes a signal, the SDK journals a cancel
// for every call issued since the previous signal.
const sdkCancels = (env) => {
  const calls = env.cur.sdkCalls;
  env.cur.sdkCalls = [];
  for (const target of calls) {
    issue(env, { c: "cancelCall", target, by: "sdk" });
    if (!env.cur || env.cur.over) return;
  }
};

const takeReady = (env, idx, push) => {
  env.cur.ready = env.cur.ready.filter((i) => i !== idx);
  env.cur.a2 = null;
  push({ type: "consume", entry: structuredClone(env.journal[idx]) });
};

// AMBIGUOUS: A5 (a cancel waiting for an unresolved call id) is not
// modelled: the SDK's cancel commands name the call's command index.
// A1: move notifications one at a time, in arrival order, into the ready
// set, and stop at the first that resolves the race. A cancel signal
// rejects the race (A4, A8). A2: members already ready are chosen by the
// SDK's completer timing, which the check leaves to the schedule.
export const vmResolve = (env, members, push) => {
  const cur = env.cur;
  const set = new Set(members);
  const hits = cur.ready.filter((i) => set.has(keyOf(env.journal[i])));
  if (hits.length === 1) {
    takeReady(env, hits[0], push);
    return "resolved";
  }
  if (hits.length > 1) {
    cur.a2 = hits;
    return "choice";
  }
  return moveArrivals(env, set, push);
};

const moveArrivals = (env, set, push) => {
  const cur = env.cur;
  while (cur.moved < cur.inbox.length) {
    const entry = env.journal[cur.inbox[cur.moved]];
    cur.moved += 1;
    if (entry.e === "cancel") {
      sdkCancels(env);
      push({ type: "consume", entry: structuredClone(entry) });
      return "resolved";
    }
    if (set.has(keyOf(entry))) {
      push({ type: "consume", entry: structuredClone(entry) });
      return "resolved";
    }
    cur.ready.push(entry.idx);
  }
  return "pending";
};

/** Resolve an A2 choice among ready members. */
export const resolveA2 = (env, idx, push) => takeReady(env, idx, push);

const startClosure = (env, idx, push) => {
  const cur = env.cur;
  const op = env.journal[idx].cmd.op;
  const sample = op === "sample";
  cur.wrappers[idx] = { state: "called", eff: -1, sample };
  if (!sample) {
    cur.effects.push({
      op, attempt: cur.n, entered: false,
      signalAbortedAtEntry: false, settled: null,
    });
    cur.wrappers[idx].eff = cur.effects.length - 1;
  }
  push({ type: "wrapper", idx });
};

// A23: start order is unspecified; the model starts closures in issue
// order, which the journal does not depend on.
// A10: a run's closure starts only when its handle is in an awaited race
// that queued notifications cannot resolve, so only after vmResolve has
// returned "pending". A run with a journaled result never starts (A27).
export const vmStartClosures = (env, members, push) => {
  let started = 0;
  for (const key of members) {
    if (!key.startsWith("r:")) continue;
    const idx = Number(key.slice(2));
    const entry = env.journal[idx];
    if (entry.cmd.c !== "run" || env.cur.wrappers[idx]) continue;
    startClosure(env, idx, push);
    started += 1;
  }
  return started;
};

// ---- closures (behaviours, abort signal, effect log) ----

const SETTLE_RAW = {
  ok: "ok", terminal: "terminal", retryable: "retryable", honour: "ok",
  ignoreOk: "ok", ignoreRetryable: "retryable", mapAbort: "ok",
};
const ABORT_RAW = { honour: "interrupted", mapAbort: "ownError" };
const LOG_OF_RAW = {
  ok: "ok", terminal: "terminal", retryable: "retryable",
  ownError: "retryable", interrupted: "aborted",
};

const behaviourOf = (env, idx) =>
  env.opText[env.journal[idx].cmd.op].behaviour;

// The `done` event: the closure itself completed, at this moment. The
// executor's `settle` follows when it learns of it.
const emitDone = (env, idx, outcome) => {
  const op = env.journal[idx].cmd.op;
  const name = op === "sample" ? `sample:${idx}` : op;
  env.cur.trace.push({ t: "done", op: name, cmdIdx: idx, outcome });
};

const settleNow = (env, idx, raw, push) => {
  const wrapper = env.cur.wrappers[idx];
  wrapper.state = "settled";
  if (wrapper.eff >= 0) env.cur.effects[wrapper.eff].settled = LOG_OF_RAW[raw];
  emitDone(env, idx, LOG_OF_RAW[raw]);
  push({ type: "settled", idx, raw });
};

// honour and mapAbort react to the signal as soon as it is aborted.
const reactToAbort = (env, idx, push) => {
  const wrapper = env.cur.wrappers[idx];
  if (!wrapper || wrapper.state !== "entered" || wrapper.sample) return;
  const raw = ABORT_RAW[behaviourOf(env, idx)];
  if (raw) settleNow(env, idx, raw, push);
};

const settleChoices = (cur) =>
  Object.entries(cur.wrappers)
    .filter(([, w]) => w.state === "entered" && !w.sample)
    .map(([idx]) => `settle:${idx}`);

const sampleChoices = (env) =>
  Object.entries(env.cur.wrappers)
    .filter(([, w]) => w.state === "entered" && w.sample)
    .flatMap(([idx]) =>
      env.limits.readings.map((r) => `sample:${idx}:${r}`));

/** A closure settles by its behaviour (the run ignores time). */
export const settleClosure = (env, idx, push) =>
  settleNow(env, idx, SETTLE_RAW[behaviourOf(env, idx)], push);

/** A clock sample's closure reads the host clock. */
export const settleSample = (env, idx, reading, push) => {
  env.sampleTime[idx] = env.trueTime;
  env.cur.wrappers[idx].state = "settled";
  emitDone(env, idx, "ok");
  push({ type: "settled", idx, raw: { reading } });
};

// A17: a run's result joins the arrival queue on the server's ack.
// AMBIGUOUS: a sample is acknowledged at once: it has no external effect,
// so losing it before the ack is the same as losing it before it ran.
// Samples have no effect log entry, since an Effect entry names an op.
const proposeResult = (env, idx, value) => {
  const cur = env.cur;
  cur.wrappers[idx].state = "returned";
  cur.lastExchange = env.trueTime;
  if (cur.wrappers[idx].sample) appendNotif(env, idx, value);
  else cur.proposals.push({ idx, value });
};

/** The server acknowledges a proposed result: it is journaled. */
export const ackProposal = (env, idx) => {
  const cur = env.cur;
  const found = cur.proposals.find((p) => p.idx === idx);
  cur.proposals = cur.proposals.filter((p) => p.idx !== idx);
  appendNotif(env, idx, found.value);
};

const ackChoices = (cur) => cur.proposals.map((p) => `ack:${p.idx}`);

/** True while the SDK has called a wrapper that has not returned. */
export const sdkBusy = (cur) =>
  Object.values(cur.wrappers).some((w) => w.state !== "returned");

// ---- the io object given to the executor ----

const live = (env) => env.cur && !env.cur.over && !env.cur.ending;

const enterClosure = (env, idx, push) => {
  const cur = env.cur;
  const wrapper = cur.wrappers[idx];
  wrapper.state = "entered";
  if (wrapper.eff >= 0) {
    cur.effects[wrapper.eff].entered = true;
    cur.effects[wrapper.eff].signalAbortedAtEntry = !!cur.signals[idx];
  }
  if (cur.signals[idx]) reactToAbort(env, idx, push);
};

const refuseClosure = (env, idx) => {
  const cur = env.cur;
  const wrapper = cur.wrappers[idx];
  wrapper.state = "refused";
  if (wrapper.eff < 0) return;
  cur.effects[wrapper.eff].signalAbortedAtEntry = !!cur.signals[idx];
  cur.effects[wrapper.eff].settled = "aborted";
};

const abortSignal = (env, idx, push) => {
  env.cur.signals[idx] = true;
  reactToAbort(env, idx, push);
};

// The VM ends the attempt on the first retryable failure proposed; later
// proposals are not accepted.
const returnRetryable = (env, idx) => {
  env.cur.wrappers[idx].state = "returned";
  env.cur.ending = "retry";
};

const writeOutput = (env, outcome) => {
  appendEntry(env, { e: "output", outcome });
  env.outcome = outcome;
  endAttempt(env, "output");
};

const decorate = (env, event) =>
  event.t === "sample"
    ? { ...event, trueTime: env.sampleTime[event.cmdIdx] ?? null }
    : event;

/** The executor's only window on the environment. */
export const makeIo = (env, push) => ({
  issue: (cmd) => (live(env) ? issue(env, cmd) : -1),
  enterClosure: (idx) => live(env) && enterClosure(env, idx, push),
  refuseClosure: (idx) => live(env) && refuseClosure(env, idx),
  abortSignal: (idx) => env.cur && abortSignal(env, idx, push),
  returnResult: (idx, value) => live(env) && proposeResult(env, idx, value),
  returnRetryable: (idx) => live(env) && returnRetryable(env, idx),
  writeOutput: (outcome) => live(env) && writeOutput(env, outcome),
  failRetryable: () => live(env) && endAttempt(env, "retry"),
  emit: (event) => env.cur && env.cur.trace.push(decorate(env, event)),
  now: () => env.trueTime,
});

// ---- time (ticks, R1, R6) ----

/** Advance true time one tick; R1's stall starts once the server's
 * inactivity timeout passes while a closure executes. */
export const tick = (env) => {
  env.trueTime += 1;
  env.ticks += 1;
  const cur = env.cur;
  if (!cur || cur.stalled || !sdkBusy(cur)) return;
  if (env.trueTime - cur.lastExchange >= env.limits.inactivity) {
    cur.stalled = true;
  }
};

// ---- endings ----

const killChildren = (env) => {
  for (const child of env.children) {
    if (child.status === "running") child.killed = true;
  }
};

// AMBIGUOUS: a proposal already on the stream is journaled before the
// suspension (the server reads the stream in order). S16(c) assumes
// nothing is lost at suspension; the register has no entry for this.
const flushProposals = (env) => {
  const pending = env.cur.proposals;
  env.cur.proposals = [];
  env.cur.over = true;
  for (const p of pending) appendNotif(env, p.idx, p.value);
};

// A wrapper the SDK called but the executor still holds (at the entry gate
// or in the freeze) when the attempt ends neither entered nor refused.
const markHeld = (cur) => {
  for (const wrapper of Object.values(cur.wrappers)) {
    if (wrapper.state === "called" && wrapper.eff >= 0) {
      cur.effects[wrapper.eff].entered = null;
    }
  }
};

const nextPhase = (env, kind, n) => {
  if (kind === "killed" || kind === "output") return "over";
  if (n + 1 >= env.limits.attempts) return "over";
  return kind === "suspended" ? "suspended" : "start";
};

/** End the current attempt. `at` defaults to the trace's last index. */
export const endAttempt = (env, kind, at) => {
  const cur = env.cur;
  if (!cur || (cur.over && kind !== "suspended")) return;
  if (kind === "suspended") flushProposals(env);
  cur.over = true;
  markHeld(cur);
  const end = { kind, at: at ?? cur.trace.length - 1 };
  if (cur.mismatch) end.detail = "mismatch";
  env.done.push({
    n: cur.n, journalIn: cur.journalIn,
    journalOut: structuredClone(env.journal),
    trace: cur.trace, effects: cur.effects, end,
  });
  if (kind === "killed") killChildren(env);
  env.cur = null;
  env.phase = nextPhase(env, kind, cur.n);
};

// ---- the schedule's choices ----

const endingChoices = (env, awaiting) => {
  const out = ["crash", "kill", "ended"];
  if (awaiting && !sdkBusy(env.cur)) out.push("suspend");
  return out;
};

// Coverage reduction (limits.observableTicks), not a lossless one. A tick
// is offered only while the SDK has a wrapper outstanding (a run or a
// sample is executing or held) or a sleep or deadline timer is pending.
// Ticks are read by a sample's trueTime, the warnings and R1's stall;
// the first two need an outstanding wrapper, and pending timers are kept
// so time can pass between a sleep's issue and its credit (P5). What is
// dropped: histories where true time passes while nothing executes and no
// timer is pending. A later sample's trueTime can still reach the same
// value through ticks in its own window, but those ticks also widen the
// stall gap, so a few stall timings are reachable only on the full
// schedule. A tick cannot simply be moved past an exchange without
// changing that gap.
const timerPending = (env) =>
  env.journal.some((entry) => entry.e === "cmd" &&
    entry.cmd.c === "sleep" && !env.notified[`r:${entry.idx}`]);

// Premise (limits.noTicksDuringSamples): a clock reading completes within
// the inactivity timeout; register entry to be filed. So no tick is
// offered while the only outstanding wrappers are clock samples, and R1's
// stall cannot start inside a sample's closure.
const onlySamplesBusy = (cur) => {
  const busy = Object.values(cur.wrappers).filter((w) =>
    w.state !== "returned");
  return busy.length > 0 && busy.every((w) => w.sample);
};

const tickOffered = (env) => {
  if (env.ticks >= env.limits.ticks) return false;
  if (env.limits.noTicksDuringSamples && onlySamplesBusy(env.cur)) {
    return false;
  }
  if (!env.limits.observableTicks) return true;
  return sdkBusy(env.cur) || timerPending(env);
};

const optionalChoices = (env) => {
  const out = [];
  if (env.cancels < env.limits.cancels) out.push("cancel");
  if (tickOffered(env)) out.push("tick");
  return out;
};

/** Every choice the environment offers. `awaiting` says whether the
 * executor is awaiting a race (suspension needs one, R1).
 * AMBIGUOUS: once the VM has accepted a retryable failure, only acks and
 * the end are offered; a cancel, crash or kill there is left out. */
export const envChoices = (env, awaiting) => {
  if (env.phase === "over") return [];
  if (env.phase === "suspended") {
    const resume = arrivalChoices(env);
    if (env.cancels < env.limits.cancels) resume.push("cancel");
    return resume;
  }
  const cur = env.cur;
  if (cur.a2) return cur.a2.map((i) => `a2:${i}`);
  if (cur.ending === "retry") return [...ackChoices(cur), "end"];
  return [
    ...arrivalChoices(env), ...settleChoices(cur), ...sampleChoices(env),
    ...ackChoices(cur), ...optionalChoices(env),
    ...endingChoices(env, awaiting),
  ];
};

/** The public part of the children, for the history. */
export const childRecords = (env) =>
  env.children.map(({ key, viaCmd, attempt, kind, ran, cancelled, killed }) =>
    ({ key, viaCmd, attempt, kind, ran, cancelled, killed }));
