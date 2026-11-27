// model.mjs: the system under test of the step 7 check as a
// nondeterministic state machine. It joins the environment (env.mjs) and
// the executor (rules.mjs) through the interface stated at the top of each,
// and generates the programs of step 7's grammar (comment 7144185705).
// The history format is HISTORY.md.
//
// API for the enumerator:
//   initial(program, options) -> state      options.mutant: a mutant name
//   choices(state) -> string[]              empty when terminal
//   step(state, choice) -> state            pure; the old state is kept
//   history(state) -> History               for a terminal state
//   programs(bounds) -> generator           bounds {fibers, statements, ops}
//   limits                                  the schedule's bounds
//   MUTANTS, CONTROL_MUTANTS                name -> one-line description

import * as env from "./env.mjs";
import * as rules from "./rules.mjs";

/** The full schedule of step 7, with no reduction. Ticks are per
 * invocation; the inactivity timeout is in ticks, so a deadline of 2 is
 * refused (C15). */
export const fullLimits = {
  cancels: 2,
  attempts: 2,
  readings: [0, 1, 2, 3],
  ticks: 3,
  inactivity: 2,
  observableTicks: false,
  pruneSilentTickEndings: false,
  noTicksDuringSamples: false,
};

/** The reduced schedule, the default. observableTicks and readings
 * {0, 2, 3} drop schedules (coverage reductions, see env.mjs's
 * tickOffered); pruneSilentTickEndings is exact (see endsInvocation);
 * noTicksDuringSamples rests on a stated premise (env.mjs). */
export const limits = {
  ...fullLimits,
  readings: [0, 2, 3],
  observableTicks: true,
  pruneSilentTickEndings: true,
  noTicksDuringSamples: true, // premise: see env.mjs's onlySamplesBusy
};

/** Each mutant is one small named deviation from part 1's rules. */
export const MUTANTS = {
  cancelOvertakes: "a cancel turn runs before results already queued (C19)",
  sampleToCancel:
    "a pending sample is given to a cancellation consumed behind it (C19)",
  noM1:
    "a queued result whose fiber stopped awaiting it still gets a turn and a " +
    "sample (M1)",
  rev5Credit:
    "a delivered sleep credits max(L + d, s), not its anchor (§4, M5)",
  deliveryAnchor:
    "a sleep's anchor is the L of its delivery turn, not of its issuing turn " +
    "(§4)",
  noEntryCheck:
    "the wrapper calls the closure even if the signal is aborted (C17)",
  noEntryGate:
    "the wrapper checks the signal without waiting for consumed causes (C24)",
  gateHoldsSamples: "clock samples wait at the entry gate like runs (M7)",
  reattachOnCancel:
    "every pending attach is issued again after a cancel signal (C22, " +
    "withdrawn by C28)",
  labelInKey: "a compensation key carries the op label after the count (M9)",
  windowCallsPlain:
    "calls issued between a cancel's consumption and its turn are plain " +
    "calls (C29)",
  lateCancelReports409:
    "a cancel absorbed after the root's exit makes the outcome a " +
    "cancellation (C30)",
  noFreeze:
    "a retryable closure failure is returned at once, without the freeze " +
    "(C18)",
  retryableFirst:
    "when the freeze ends, the retryable failure is returned before " +
    "journaled outcomes (M2)",
  deadlineByLocalSettle:
    "a deadline is beaten by the closure settling locally, not by journal " +
    "order (C23)",
  dropUnstarted:
    "an interrupted fiber's unstarted runs leave the race instead of being " +
    "retained (C12)",
  noClosingAckWait:
    "closing writes Output without waiting for settled runs' results (C20)",
  cancelCompensation:
    "the executor cancels a compensation child when its waiter is " +
    "interrupted (C27)",
  idsRacedLate:
    "a call's invocation id joins the race only once the call must be " +
    "cancelled (M6)",
  handlerScheduler:
    "a run's Effect needs a turn to finish, so it cannot settle during the " +
    "freeze (M8)",
};

/** Mutants that are a control for one check. They stay out of MUTANTS,
 * which merged.check.mjs and check.mjs iterate. hostTimeLink is the
 * control of tick.check.mjs: it needs a sleep but no clock read, so it
 * can fail among the programs the tier explores without ticks. */
export const CONTROL_MUTANTS = {
  hostTimeLink: "a sleep link is shortened by the host clock (time read " +
    "outside the durable services)",
};

// ---- the state machine ----

const configOf = (state) => ({
  invocationId: state.env.invocationId,
  inactivity: state.limits.inactivity,
  mutant: state.mutant,
});

const ioOf = (state) =>
  env.makeIo(state.env, (event) => state.queue.push(event));

const dispatch = (state, io, event) => {
  const exec = state.exec;
  if (event.type === "consume") rules.onConsume(exec, io, event.entry);
  if (event.type === "wrapper") rules.onWrapperCalled(exec, io, event.idx);
  if (event.type === "settled") {
    rules.onClosureSettled(exec, io, event.idx, event.raw);
  }
};

const attemptLive = (state) =>
  state.env.phase === "attempt" && state.env.cur &&
  !state.env.cur.over && !state.env.cur.ending && !state.env.cur.a2;

// The VM resolves the race from queued notifications, or starts closures.
const vmStep = (state, io) => {
  const members = rules.raceMembers(state.exec);
  if (members === null) return false;
  const push = (event) => state.queue.push(event);
  const resolved = env.vmResolve(state.env, members, push);
  if (resolved !== "pending") return resolved === "resolved";
  return env.vmStartClosures(state.env, members, push) > 0;
};

// Run everything deterministic until the next choice is needed.
const quiesce = (state) => {
  const io = ioOf(state);
  for (let guard = 0; guard < 100000; guard += 1) {
    if (!attemptLive(state)) break;
    if (state.queue.length > 0) {
      dispatch(state, io, state.queue.shift());
      continue;
    }
    if (rules.progress(state.exec, io)) continue;
    if (!vmStep(state, io)) break;
  }
  if (attemptLive(state)) rules.checkWarnings(state.exec, io);
};

const beginAttempt = (state) => {
  env.beginAttempt(state.env);
  state.queue = [];
  state.exec = rules.createExecutor(state.program, configOf(state));
  rules.startAttempt(state.exec, ioOf(state));
  quiesce(state);
};

// After an ending, Restate retries at once; a suspension waits for a
// resume (handled in step).
const settle = (state) => {
  quiesce(state);
  while (state.env.phase === "start") beginAttempt(state);
};

/** The initial state for `program`; options.mutant selects a mutant. */
export const initial = (program, options = {}) => {
  const lim = { ...limits, ...(options.limits ?? {}) };
  const state = {
    program, mutant: options.mutant ?? null, limits: lim,
    env: env.newEnv(program, lim), exec: null, queue: [], silentTick: false,
  };
  settle(state);
  return state;
};

/** Every choice available, as labels. Empty when terminal. */
// Exact reduction (limits.pruneSilentTickEndings). A silent tick added no
// trace event and did not start R1's stall, so it changed only true time
// and the tick count. An ending that finishes the invocation (a kill, or
// any ending in the last allowed attempt) leaves nothing that could read
// true time afterwards. It was also offered before the tick: a tick changes
// no wrapper, race or phase. So [silent tick, ending] gives the same
// history, as JSON, as [ending] taken just before the tick, which is
// still explored. Only that ending is skipped.
const endsInvocation = (state, choice) => {
  if (choice === "kill") return true;
  const final = state.env.cur &&
    state.env.cur.n + 1 >= state.limits.attempts;
  return final && ["crash", "ended", "suspend"].includes(choice);
};

export const choices = (state) => {
  const awaiting = state.exec !== null &&
    rules.raceMembers(state.exec) !== null;
  const all = env.envChoices(state.env, awaiting);
  if (!state.silentTick || !state.limits.pruneSilentTickEndings) return all;
  const kept = all.filter((choice) => !endsInvocation(state, choice));
  // A state left with no choice would look terminal with its attempt
  // still open, so the endings stay when nothing else is offered.
  return kept.length > 0 ? kept : all;
};

const endWith = (state, kind, at) => {
  state.queue = [];
  env.endAttempt(state.env, kind, at);
};

const ENDINGS = {
  crash: (state) => endWith(state, "crashed"),
  kill: (state) => endWith(state, "killed"),
  suspend: (state) => endWith(state, "suspended"),
  end: (state) => endWith(state, "retry"),
  ended: (state) => {
    const at = state.env.cur.trace.length - 1;
    rules.onEnded(state.exec, ioOf(state));
    endWith(state, "ended", at);
  },
};

const push = (state) => (event) => state.queue.push(event);

const ACTIONS = {
  fire: (state, idx) => env.applyArrival(state.env, "fire", idx),
  id: (state, idx) => env.applyArrival(state.env, "id", idx),
  done: (state, idx) => env.applyArrival(state.env, "done", idx),
  settle: (state, idx) => env.settleClosure(state.env, idx, push(state)),
  sample: (state, idx, reading) =>
    env.settleSample(state.env, idx, reading, push(state)),
  ack: (state, idx) => env.ackProposal(state.env, idx),
  a2: (state, idx) => env.resolveA2(state.env, idx, push(state)),
  cancel: (state) => env.appendCancel(state.env),
  tick: (state) => {
    env.tick(state.env);
    if (state.env.cur && state.exec) rules.onTick(state.exec, ioOf(state));
  },
};

const applyChoice = (state, choice) => {
  const [name, a, b] = choice.split(":");
  if (ENDINGS[name]) return ENDINGS[name](state);
  ACTIONS[name](state, Number(a), Number(b));
};

// What a tick could change that a history shows: the attempt's trace and
// whether R1's stall has started.
const visible = (state) => {
  const cur = state.env.cur;
  return cur ? `${cur.n}:${cur.trace.length}:${cur.stalled}` : "none";
};

/** Take one choice. The old state is not changed. */
export const step = (state, choice) => {
  if (!choices(state).includes(choice)) {
    throw new Error(`not an available choice: ${choice}`);
  }
  const next = structuredClone(state);
  const resuming = next.env.phase === "suspended";
  const seen = visible(next);
  applyChoice(next, choice);
  if (resuming) next.env.phase = "start";
  settle(next);
  next.silentTick = choice === "tick" && visible(next) === seen;
  if (next.env.phase === "suspended" && choices(next).length === 0) {
    next.env.phase = "over";
  }
  return next;
};

/** The history of a terminal state (HISTORY.md). */
export const history = (state) => ({
  program: state.program,
  attempts: state.env.done.map((a) => ({
    n: a.n, journalIn: a.journalIn, journalOut: a.journalOut,
    trace: a.trace, effects: a.effects, end: a.end,
  })),
  outcome: state.env.outcome,
  children: env.childRecords(state.env),
});

// ---- the event stream (HISTORY.md, "The event stream") ----

const terminal = (state) => choices(state).length === 0;

const attemptItems = (record) => [
  { s: "attemptStart", n: record.n, journalIn: record.journalIn },
  ...record.trace.map((event) => ({ s: "event", event })),
];

const endItem = (record) => ({
  s: "attemptEnd", end: record.end, journalOut: record.journalOut,
  effects: record.effects,
});

/** Everything that has happened up to `state`, as monitor items. It is
 * stable: the stream of an earlier state on the same path is a prefix.
 * Items already emitted are never changed later: a finished attempt's
 * record is fixed, the open attempt's trace only grows, and its end and
 * the invocation's end appear only once they happen. */
export const streamOf = (state) => {
  const items = [{ s: "program", program: state.program }];
  for (const record of state.env.done) {
    items.push(...attemptItems(record), endItem(record));
  }
  if (state.env.cur) items.push(...attemptItems(state.env.cur));
  if (terminal(state)) {
    items.push({ s: "invocationEnd", outcome: state.env.outcome,
      children: env.childRecords(state.env) });
  }
  return items;
};

// ---- the canonical state key ----

// The open attempt, without what is already in the stream and read by no
// later step:
// - trace: excluded, but its length kept. Later steps only append to it.
//   Its length is read by an ending (End.at, emitted in attemptEnd) and
//   by the silent-tick test, which compares lengths before and after.
// - journalIn: excluded. It was emitted in attemptStart and nothing reads
//   it again (replay reads env.journal through `replay` and `cursor`).
// - effects: kept whole. Entries are still changed (entered, settled,
//   entered null at the end) and are emitted only in attemptEnd.
// - every other field (inbox, moved, ready, a2, replay, cursor, sdkCalls,
//   wrappers, signals, proposals, stalled, lastExchange, ending, over,
//   mismatch, n): kept. The VM, the stall and the endings read them.
const curKey = (cur) => {
  if (!cur) return null;
  const { trace, journalIn, ...rest } = cur;
  return { ...rest, traceLength: trace.length };
};

// The environment:
// - done (finished attempts' records): excluded, but its count kept. They
//   are in the stream and nothing reads them except the count, which
//   numbers the next attempt.
// - limits, opText, invocationId: excluded here because they are fixed by
//   the program and the limits, which the key holds at its top.
// - journal, notified, trueTime, ticks, cancels, phase, outcome, children,
//   childOfCmd, childOfKey, sampleTime: kept. The server, the VM, the
//   schedule's bounds, R1's stall, the samples' trueTime (sampleTime is
//   read again when a journaled sample is replayed), the Output and the
//   children (emitted in invocationEnd) read them.
const envKey = (e) => {
  const { done, limits: _l, opText: _o, invocationId: _i, cur, ...rest } = e;
  return { ...rest, doneCount: done.length, cur: curKey(cur) };
};

// The executor: kept whole except its copy of the program and its config,
// which the key holds at its top. Its fibers, operations, cause queue,
// pending sample, L and the sleeps' anchors, opCount (compensation keys),
// draws, wrappers, aborts and their times, freeze, closing and warnings
// all decide later steps. It is excluded when dead, that is outside an
// open attempt or once the VM has accepted a retryable failure: no
// choice or step then reads it, and a new attempt builds a fresh one.
const execKey = (state) => {
  const cur = state.env.cur;
  if (state.env.phase !== "attempt" || !cur || cur.ending) return null;
  const { program: _p, cfg: _c, ...rest } = state.exec;
  return rest;
};

/** A canonical key: two states with equal keys have the same choices and,
 * for every choice, steps to states with equal keys that append the same
 * new stream items. Object key order is kept, not sorted, because the
 * model iterates objects in insertion order. The queue is empty between
 * steps, and silentTick is kept because it filters the choices. */
export const stateKey = (state) => JSON.stringify({
  program: state.program, mutant: state.mutant, limits: state.limits,
  silentTick: state.silentTick, queue: state.queue,
  env: envKey(state.env), exec: execKey(state),
});

// ---- the grammar (HISTORY.md, step 7) ----

const BEHAVIOURS = ["ok", "terminal", "retryable", "honour", "ignoreOk",
  "ignoreRetryable", "mapAbort"];
const DEADLINES = [undefined, 1, 2];
const SLEEPS = [0, 1, 2, 3];
const RESULTS = ["ok", "terminal"];

const withOp = (st, fiber, kind) => {
  const counts = { ...st.counts, [kind]: st.counts[kind] + 1 };
  const name = `${kind}${counts[kind]}`;
  const avail = { ...st.avail, [fiber]: [...st.avail[fiber], name] };
  return { st: { ...st, counts, avail, ops: st.ops + 1 }, name };
};

function* genOps(st, fiber, bounds) {
  if (st.ops >= bounds.ops) return;
  const run = withOp(st, fiber, "r");
  for (const behaviour of BEHAVIOURS) {
    for (const deadline of DEADLINES) {
      const stmt = { s: "run", op: run.name, behaviour };
      if (deadline !== undefined) stmt.deadline = deadline;
      yield { stmt, st: run.st, used: 1, term: false };
    }
  }
  const sleep = withOp(st, fiber, "s");
  for (const ms of SLEEPS) {
    yield { stmt: { s: "sleep", op: sleep.name, ms }, st: sleep.st, used: 1 };
  }
  const call = withOp(st, fiber, "c");
  for (const result of RESULTS) {
    yield { stmt: { s: "call", op: call.name, result }, st: call.st, used: 1 };
  }
}

const without = (st, fiber, names) => ({
  ...st,
  avail: { ...st.avail,
    [fiber]: st.avail[fiber].filter((n) => !names.includes(n)) },
});

function* genAwaits(st, fiber) {
  const avail = st.avail[fiber];
  for (const op of avail) {
    yield { stmt: { s: "await", op }, st: without(st, fiber, [op]), used: 1 };
  }
  for (const a of avail) {
    for (const b of avail) {
      if (a === b) continue;
      const stmt = { s: "race", ops: [a, b] };
      yield { stmt, st: without(st, fiber, [a, b]), used: 1 };
    }
  }
}

function* genSimple(st, fiber, bounds) {
  if (fiber === "f0" && st.forked === null && bounds.fibers >= 2) {
    for (const daemon of [false, true]) {
      const stmt = { s: "fork", fiber: "f1" };
      yield { stmt, st: { ...st, forked: daemon }, used: 1 };
    }
  }
  for (const s of ["clock", "draw"]) yield { stmt: { s }, st, used: 1 };
  yield { stmt: { s: "return" }, st, used: 1, term: true };
  for (const kind of ["terminal", "retryable"]) {
    yield { stmt: { s: "fail", kind }, st, used: 1, term: true };
  }
}

function* genUninterruptible(st, budget, fiber, bounds) {
  for (const inner of genStmt(st, budget - 1, fiber, bounds)) {
    const stmt = { s: "uninterruptible", body: [inner.stmt] };
    yield { stmt, st: inner.st, used: inner.used + 1, term: !!inner.term };
  }
}

// A finalizer sees only operations started before the ensuring or in the
// finalizer itself: the body may have been interrupted before it started
// its own (a program could not refer to them).
const finalizerScope = (before, afterBody, fiber) => ({
  ...afterBody,
  avail: { ...afterBody.avail, [fiber]: afterBody.avail[fiber]
    .filter((n) => before.avail[fiber].includes(n)) },
});

function* genEnsuring(st, budget, fiber, bounds) {
  for (const body of genBlock(st, budget - 2, fiber, bounds)) {
    if (body.stmts.length === 0) continue;
    const scoped = finalizerScope(st, body.st, fiber);
    const finBudget = Math.min(2, budget - 1 - body.used);
    for (const fin of genBlock(scoped, finBudget, fiber, bounds)) {
      if (fin.stmts.length === 0) continue;
      const stmt = { s: "ensuring", body: body.stmts, finalizer: fin.stmts };
      const next = mergeScopes(body.st, scoped, fin.st, fiber);
      yield { stmt, st: next, used: 1 + body.used + fin.used,
        term: !!(body.term || fin.term) };
    }
  }
}

// After an ensuring: the body's operations stay available unless the
// finalizer awaited them; the finalizer's own new ones are added.
const mergeScopes = (afterBody, scoped, afterFin, fiber) => {
  const awaitedInFin = scoped.avail[fiber]
    .filter((n) => !afterFin.avail[fiber].includes(n));
  const startedInFin = afterFin.avail[fiber]
    .filter((n) => !scoped.avail[fiber].includes(n));
  const kept = afterBody.avail[fiber].filter((n) => !awaitedInFin.includes(n));
  return { ...afterFin,
    avail: { ...afterFin.avail, [fiber]: [...kept, ...startedInFin] } };
};

function* genStmt(st, budget, fiber, bounds) {
  if (budget < 1) return;
  yield* genOps(st, fiber, bounds);
  yield* genAwaits(st, fiber);
  yield* genSimple(st, fiber, bounds);
  if (budget >= 2) yield* genUninterruptible(st, budget, fiber, bounds);
  if (budget >= 3) yield* genEnsuring(st, budget, fiber, bounds);
}

function* genBlock(st, budget, fiber, bounds) {
  yield { stmts: [], st, used: 0, term: false };
  for (const head of genStmt(st, budget, fiber, bounds)) {
    if (head.term) {
      yield { stmts: [head.stmt], st: head.st, used: head.used, term: true };
      continue;
    }
    for (const tail of genBlock(head.st, budget - head.used, fiber, bounds)) {
      yield { stmts: [head.stmt, ...tail.stmts], st: tail.st,
        used: head.used + tail.used, term: tail.term };
    }
  }
}

// A trailing `return` at a fiber's top level equals falling off its end.
const trailingReturn = (stmts) =>
  stmts.length > 0 && stmts[stmts.length - 1].s === "return";

const EMPTY = { counts: { r: 0, s: 0, c: 0 }, ops: 0,
  avail: { f0: [], f1: [] }, forked: null };

/** Every program of the grammar within `bounds`. Names are given in text
 * order per kind, so programs equal up to renaming appear once. */
export function* programs(bounds) {
  for (const root of genBlock(EMPTY, bounds.statements, "f0", bounds)) {
    if (trailingReturn(root.stmts)) continue;
    const f0 = { id: "f0", daemon: false, body: root.stmts };
    if (root.st.forked === null) {
      yield { fibers: [f0] };
      continue;
    }
    const left = bounds.statements - root.used;
    for (const child of genBlock(root.st, left, "f1", bounds)) {
      if (child.stmts.length === 0 || trailingReturn(child.stmts)) continue;
      const f1 = { id: "f1", daemon: root.st.forked, body: child.stmts };
      yield { fibers: [f0, f1] };
    }
  }
}
