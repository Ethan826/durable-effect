// rules.mjs: the executor of design revision 6, part 1 (comment
// 7142428658), as the system under test of the step 7 check. It also holds
// a small stand-in for Effect's runtime (fibers, masks, finalizers,
// structured concurrency), taken as given by the interface I1 to I9 of #37.
// A turn is atomic (X4's slices are excluded by step 7).
//
// Interface with the environment (env.mjs). Nothing else crosses it.
//   The executor calls only these methods of `io`:
//     issue(cmd) -> idx, enterClosure(idx), refuseClosure(idx),
//     abortSignal(idx), returnResult(idx, value), returnRetryable(idx),
//     writeOutput(outcome), failRetryable(), emit(event), now()
//   The environment, through model.mjs, calls:
//     createExecutor(program, config)  config: {invocationId, inactivity,
//                                      mutant}
//     startAttempt(exec, io)           the first turn issues its sample
//     raceMembers(exec)                null when not awaiting; else keys
//                                      "r:<idx>" and "i:<idx>"
//     onConsume(exec, io, entry)       the race resolved with entry
//     onWrapperCalled(exec, io, idx)   the SDK called the run's wrapper
//     onClosureSettled(exec, io, idx, raw)
//     onEnded(exec, io)                Restate's abort timeout (C7)
//     onTick(exec, io)                 the executor's timer (warnings)
//     progress(exec, io) -> boolean    one deterministic step, if any
//     checkWarnings(exec, io)          the first warning (C16)

const MAX_SAFE = 2 ** 53 - 1;
const LINK_MAX = 2; // step 7's maximum link length, standing in for 2^31-1

const mutant = (exec, name) => exec.cfg.mutant === name;

/** A fresh executor for one attempt. */
export const createExecutor = (program, config) => ({
  cfg: config, program,
  fibers: {}, runQueue: [], ops: {}, byCmd: {},
  causes: [], turnCause: null, sampleIdx: null, causeSeq: 0, acted: {},
  L: null, opCount: 0,
  cancelConsumed: false, cancelled: false, lateCancel: false,
  rootExit: null, closing: false, closingTurn: false, violations: [],
  frozen: false, held: [], heldOk: [], deferred: [], inTurn: false,
  wrappers: {}, unconsumed: {}, aborted: {}, abortTime: {}, gone: {},
  draws: 0, warned1: false, warned2: {}, lastVisible: 0, over: false,
});

// ---- commands (§6's count) ----

const issueCmd = (exec, io, cmd, fiber) => {
  const idx = io.issue(cmd);
  if (cmd.c !== "cancelCall") exec.opCount += 1;
  io.emit({ t: "issue", fiber, cmdIdx: idx, cmd });
  exec.lastVisible = io.now();
  return idx;
};

const issueSample = (exec, io) => {
  const idx = issueCmd(exec, io, { c: "run", op: "sample" }, null);
  exec.sampleIdx = idx;
  exec.byCmd[idx] = { role: "sample" };
};

/** The first turn takes a sample before the root starts (§4). */
export const startAttempt = (exec, io) => {
  exec.lastVisible = io.now();
  exec.turnCause = { kind: "first" };
  exec.inTurn = true;
  io.emit({ t: "turn", cause: "first" });
  issueSample(exec, io);
  exec.inTurn = false;
};

// ---- the race (§3, S4, M6) ----

const runKeys = (exec, op) => {
  const out = [];
  const live = op.status === "pending" || op.retained;
  if (!op.consumed && live) out.push(`r:${op.idx}`);
  const settledLocally = mutant(exec, "deadlineByLocalSettle") &&
    ["settled", "done"].includes(exec.wrappers[op.idx]?.state);
  const deadlineLive = op.deadlineIdx !== null && !op.deadlineConsumed &&
    !op.consumed && !op.dropped && !settledLocally;
  if (deadlineLive) out.push(`r:${op.deadlineIdx}`);
  return out;
};

const idWanted = (exec, op) =>
  !op.idArrived &&
  (op.send || !mutant(exec, "idsRacedLate") || op.mustCancel);

const callKeys = (exec, op) => {
  const out = [];
  if (idWanted(exec, op)) out.push(`i:${op.idx}`);
  const waiting = op.status === "pending" && !op.consumed;
  if (waiting && !op.send) out.push(`r:${op.idx}`);
  const attachLive = op.attachIdx !== null && !op.attachRetired;
  if (waiting && op.send && attachLive) out.push(`r:${op.attachIdx}`);
  return out;
};

const opKeys = (exec, op) => {
  if (op.kind === "run") return runKeys(exec, op);
  if (op.kind === "call") return callKeys(exec, op);
  const waiting = op.status === "pending" && !op.consumed;
  return waiting && op.idx !== null ? [`r:${op.idx}`] : [];
};

/** The members of the race the executor awaits, or null if it awaits
 * none. Every pending operation is a member (§3). */
export const raceMembers = (exec) => {
  if (exec.over) return null;
  const keys = Object.values(exec.ops).flatMap((op) => opKeys(exec, op));
  if (exec.sampleIdx !== null) keys.push(`r:${exec.sampleIdx}`);
  const members = keys.filter((key) => !exec.gone[key]);
  return members.length > 0 ? members : null;
};

// ---- aborts (§7.2, §7.3, C7, S18) ----

const abortRun = (exec, io, op, cause) => {
  if (exec.aborted[op.idx]) return;
  exec.aborted[op.idx] = true;
  exec.abortTime[op.idx] = io.now();
  io.emit({ t: "abort", op: op.op, cause });
  io.abortSignal(op.idx);
};

const cancelCallOp = (exec, io, op) => {
  if (op.cancelIssued) return;
  if (!op.idArrived) {
    op.mustCancel = true;
    return;
  }
  op.cancelIssued = true;
  const cmd = { c: "cancelCall", target: op.idx, by: "executor" };
  issueCmd(exec, io, cmd, null);
};

// C12; dropUnstarted is C12 off. AMBIGUOUS: a run whose result the race
// has already consumed (queued behind a sample) is not aborted again; §7.2
// says "aborts" without that condition.
const releaseRun = (exec, io, op) => {
  if (op.consumed) return;
  const unstarted = !exec.wrappers[op.idx];
  if (mutant(exec, "dropUnstarted") && unstarted) op.dropped = true;
  else op.retained = true;
  abortRun(exec, io, op, "interrupt");
};

// §3, C27, C29: a compensation send is never cancelled.
const releaseCall = (exec, io, op) => {
  if (op.consumed) return;
  if (!op.send) return cancelCallOp(exec, io, op);
  op.attachRetired = true;
  if (!op.compensation || mutant(exec, "cancelCompensation")) {
    cancelCallOp(exec, io, op);
  }
};

/** A fiber stops awaiting or owning an operation (§3). `cause` is
 * "interrupt", "race" (a lost race) or "exit" (the fiber exited with the
 * operation started and not consumed, as a forked child is interrupted). */
const releaseOp = (exec, io, op, cause) => {
  if (op.status !== "pending") return;
  op.status = "released";
  io.emit({ t: "release", fiber: op.fiber, op: op.op, cause });
  if (op.kind === "run") releaseRun(exec, io, op);
  if (op.kind === "call") releaseCall(exec, io, op);
};

// ---- the fiber runtime (stand-in for Effect; I4, I6, I8) ----

const NO_ERRORS = { interrupt: null, errors: [] };

const combine = (first, second) => ({
  interrupt: first.interrupt || second.interrupt,
  errors: [...first.errors, ...second.errors],
});

const failure = (kind, detail) => ({ interrupt: null,
  errors: [{ kind, detail }] });

const isOk = (value) => value && value.ok !== undefined;

const errorOf = (op) => `${op.op}:${op.result.terminal ?? op.result.defect}`;

const spawnFiber = (exec, io, id, parent) => {
  const text = exec.program.fibers.find((fiber) => fiber.id === id);
  exec.fibers[id] = {
    id, daemon: text.daemon, parent, status: "ready", mask: 0,
    frames: [{ k: "block", stmts: text.body, i: 0 }],
    interrupt: null, unwind: null, wait: null, resume: null, exit: null,
  };
  exec.runQueue.push(id);
  // X6.3: a fiber registering during closing is interrupted at once.
  if (exec.closingTurn) {
    interruptFiber(exec, io, exec.fibers[id], "closing");
  }
  if (id === "f0" && exec.cancelled) {
    interruptFiber(exec, io, exec.fibers[id], "cancel");
  }
};

const makeReady = (exec, fiber) => {
  fiber.status = "ready";
  fiber.wait = null;
  if (!exec.runQueue.includes(fiber.id)) exec.runQueue.push(fiber.id);
};

/** Interrupt a fiber. A masked fiber keeps its await (I4).
 * AMBIGUOUS: only the awaited operations are released here; the fiber's
 * other started operations are released when it exits (a started
 * operation behaves as a forked child of the fiber). A fiber that has
 * finished its body and is joining its children is not interrupted. */
const interruptFiber = (exec, io, fiber, cause) => {
  if (fiber.status === "done" || fiber.status === "joining") return;
  io.emit({ t: "interrupt", fiber: fiber.id, cause });
  if (!fiber.interrupt) fiber.interrupt = cause;
  if (fiber.mask > 0 || fiber.status !== "blocked") return;
  for (const name of fiber.wait.ops) {
    releaseOp(exec, io, exec.ops[name], "interrupt");
  }
  makeReady(exec, fiber);
};

const liveChildren = (exec, fiber) =>
  Object.values(exec.fibers).filter((f) =>
    f.parent === fiber.id && f.status !== "done");

// AMBIGUOUS: Effect interrupts a forked child when its parent completes
// and waits for it before the parent's exit is reported. The child's
// interrupt cause is taken from the parent's, or "closing" otherwise.
const finishFiber = (exec, io, fiber, exit) => {
  for (const op of Object.values(exec.ops)) {
    if (op.fiber === fiber.id) releaseOp(exec, io, op, "exit");
  }
  const children = liveChildren(exec, fiber);
  if (children.length === 0) return completeFiber(exec, io, fiber, exit);
  fiber.status = "joining";
  fiber.exit = exit;
  for (const child of children) {
    interruptFiber(exec, io, child, exit.interrupt ?? "closing");
  }
};

const completeFiber = (exec, io, fiber, exit) => {
  fiber.status = "done";
  fiber.exit = exit;
  if (fiber.id === "f0") rootExited(exec, io, exit);
  const parent = exec.fibers[fiber.parent];
  const waiting = parent && parent.status === "joining";
  if (waiting && liveChildren(exec, parent).length === 0) {
    completeFiber(exec, io, parent, parent.exit);
  }
};

// AMBIGUOUS: an interrupt that becomes applicable while the fiber is
// already unwinding (for instance after `return` ran a finalizer) is added
// to the exit's cause, as Effect adds Interrupt to a cause.
const applyInterrupt = (fiber) => {
  if (!fiber.interrupt || fiber.mask > 0) return;
  if (fiber.unwind && fiber.unwind.interrupt) return;
  const exit = { interrupt: fiber.interrupt, errors: [] };
  fiber.unwind = fiber.unwind ? combine(fiber.unwind, exit) : exit;
};

const applyResume = (fiber) => {
  const resume = fiber.resume;
  fiber.resume = null;
  if (resume && resume.fail) fiber.unwind = failure("terminal", resume.fail);
};

// Unwinding pops frames; an ensuring frame runs its finalizer masked.
const unwindStep = (exec, io, fiber) => {
  const top = fiber.frames.pop();
  if (!top) {
    finishFiber(exec, io, fiber, fiber.unwind);
    return false;
  }
  if (top.k === "mask") fiber.mask -= 1;
  if (top.k === "fin") {
    fiber.mask -= 1;
    fiber.unwind = top.exit ? combine(top.exit, fiber.unwind) : fiber.unwind;
  }
  if (top.k === "ensure") enterFinalizer(fiber, top, fiber.unwind);
  return true;
};

const enterFinalizer = (fiber, frame, exit) => {
  fiber.frames.push({ k: "fin", exit });
  fiber.mask += 1;
  fiber.frames.push({ k: "block", stmts: frame.fin, i: 0 });
  fiber.unwind = null;
};

// A block ended normally; its parent frame decides what follows.
const closeFrame = (fiber) => {
  const top = fiber.frames[fiber.frames.length - 1];
  if (!top || top.k === "block") return;
  fiber.frames.pop();
  if (top.k === "mask") fiber.mask -= 1;
  if (top.k === "ensure") enterFinalizer(fiber, top, null);
  if (top.k === "fin") {
    fiber.mask -= 1;
    fiber.unwind = top.exit;
  }
};

const normalStep = (exec, io, fiber) => {
  const top = fiber.frames[fiber.frames.length - 1];
  if (!top) {
    finishFiber(exec, io, fiber, NO_ERRORS);
    return false;
  }
  if (top.i >= top.stmts.length) {
    fiber.frames.pop();
    closeFrame(fiber);
    return true;
  }
  const stmt = top.stmts[top.i];
  top.i += 1;
  return execStmt(exec, io, fiber, stmt);
};

const stepFiber = (exec, io, fiber) => {
  for (let guard = 0; guard < 10000; guard += 1) {
    applyResume(fiber);
    applyInterrupt(fiber);
    const more = fiber.unwind
      ? unwindStep(exec, io, fiber)
      : normalStep(exec, io, fiber);
    if (!more) return;
  }
};

/** Run every runnable fiber until none is (one atomic turn, X4). */
const runFibers = (exec, io) => {
  while (exec.runQueue.length > 0 && !exec.over) {
    const fiber = exec.fibers[exec.runQueue.shift()];
    if (fiber.status === "ready") stepFiber(exec, io, fiber);
  }
};

// ---- statements ----

const pushBlock = (fiber, kind, body, extra) => {
  fiber.frames.push({ k: kind, ...extra });
  fiber.frames.push({ k: "block", stmts: body, i: 0 });
};

const execStmt = (exec, io, fiber, stmt) => {
  const handler = STATEMENTS[stmt.s];
  return handler(exec, io, fiber, stmt);
};

const STATEMENTS = {
  run: (exec, io, fiber, stmt) => startOp(exec, io, fiber, stmt),
  sleep: (exec, io, fiber, stmt) => startOp(exec, io, fiber, stmt),
  call: (exec, io, fiber, stmt) => startOp(exec, io, fiber, stmt),
  await: (exec, io, fiber, stmt) => awaitOps(exec, io, fiber, [stmt.op]),
  race: (exec, io, fiber, stmt) => awaitOps(exec, io, fiber, stmt.ops),
  fork: (exec, io, fiber, stmt) => forkStmt(exec, io, fiber, stmt),
  uninterruptible: (exec, io, fiber, stmt) => {
    fiber.mask += 1;
    pushBlock(fiber, "mask", stmt.body, {});
    return true;
  },
  ensuring: (exec, io, fiber, stmt) => {
    pushBlock(fiber, "ensure", stmt.body, { fin: stmt.finalizer });
    return true;
  },
  clock: (exec, io, fiber) => {
    io.emit({ t: "clock", fiber: fiber.id, L: exec.L });
    return true;
  },
  draw: (exec, io, fiber) => {
    io.emit({ t: "draw", fiber: fiber.id, value: drawValue(exec) });
    return true;
  },
  return: (exec, io, fiber) => {
    fiber.unwind = NO_ERRORS;
    return true;
  },
  fail: (exec, io, fiber, stmt) => {
    fiber.unwind = failure(stmt.kind, "fail");
    return true;
  },
};

const forkStmt = (exec, io, fiber, stmt) => {
  const text = exec.program.fibers.find((f) => f.id === stmt.fiber);
  spawnFiber(exec, io, stmt.fiber, text.daemon ? null : fiber.id);
  return true;
};

// §10, C10: one seeded stream per invocation, in the order the scheduler
// asks. A xorshift stream stands in for ISAAC; only its determinism matters.
const drawValue = (exec) => {
  let h = 2166136261;
  for (const ch of exec.cfg.invocationId) {
    h = Math.imul(h ^ ch.charCodeAt(0), 16777619) >>> 0;
  }
  for (let k = 0; k <= exec.draws; k += 1) {
    h ^= h << 13; h >>>= 0; h ^= h >>> 17; h ^= h << 5; h >>>= 0;
  }
  exec.draws += 1;
  return h % 1000;
};

// ---- starting durable operations (§4, §6, §7.3, §8) ----

const newOp = (exec, fiber, stmt, kind) => {
  const op = {
    op: stmt.op, kind, fiber: fiber.id, status: "pending", idx: null,
    consumed: false, result: null, deadlineIdx: null,
    deadlineConsumed: false, retained: false, dropped: false,
    links: [], anchor: null, linkMs: 0,
    send: false, compensation: false, idArrived: false, mustCancel: false,
    cancelIssued: false, attachIdx: null, attachRetired: false,
  };
  exec.ops[stmt.op] = op;
  return op;
};

const refuseOp = (op, fiber, value, kind) => {
  op.status = "done";
  op.result = value;
  fiber.unwind = failure(kind, errorOf(op));
  return true;
};

const startOp = (exec, io, fiber, stmt) => {
  const op = newOp(exec, fiber, stmt, stmt.s);
  // §8, C8: a durable start during closing is refused with a defect.
  if (exec.closing) {
    recordViolation(exec, io, "refusedAtClosing");
    return refuseOp(op, fiber, { defect: "refused" }, "defect");
  }
  if (stmt.s === "run") return startRun(exec, io, fiber, op, stmt);
  if (stmt.s === "sleep") return startSleep(exec, io, op, stmt.ms);
  return startCall(exec, io, op);
};

// §7.3, C15. AMBIGUOUS: the refusal's typed error is modelled as a
// terminal failure of the run, delivered to the fiber that starts it.
const startRun = (exec, io, fiber, op, stmt) => {
  const deadline = stmt.deadline;
  if (deadline !== undefined && deadline >= exec.cfg.inactivity) {
    return refuseOp(op, fiber, { terminal: "deadlineRefused" }, "terminal");
  }
  op.idx = issueCmd(exec, io, { c: "run", op: op.op }, fiber.id);
  exec.byCmd[op.idx] = { role: "op", op: op.op };
  if (deadline === undefined) return true;
  const cmd = { c: "sleep", op: "deadline", ms: deadline };
  op.deadlineIdx = issueCmd(exec, io, cmd, fiber.id);
  exec.byCmd[op.deadlineIdx] = { role: "deadline", op: op.op };
  return true;
};

const splitLinks = (ms) => {
  const links = [];
  for (let left = ms; left > 0; left -= Math.min(left, LINK_MAX)) {
    links.push(Math.min(left, LINK_MAX));
  }
  return links.length > 0 ? links : [0];
};

// §4: each link records its anchor, the L of the turn that issues it.
const issueLink = (exec, io, op) => {
  op.linkMs = op.links.shift();
  op.anchor = exec.L;
  op.consumed = false;
  const cmd = { c: "sleep", op: op.op, ms: op.linkMs };
  op.idx = issueCmd(exec, io, cmd, op.fiber);
  exec.byCmd[op.idx] = { role: "op", op: op.op };
};

const startSleep = (exec, io, op, ms) => {
  op.links = splitLinks(ms);
  issueLink(exec, io, op);
  return true;
};

// C3, M9: the key is exactly `<invocation id>:<n>`, n the count of
// operations issued before this send. labelInKey adds the label.
const sendKey = (exec, op) => {
  const base = `${exec.cfg.invocationId}:${exec.opCount}`;
  return mutant(exec, "labelInKey") ? `${base}:${op.op}` : base;
};

// C29: every call issued after a cancel signal has been consumed is a
// one-way send awaited through attach. windowCallsPlain is C29 off: only
// calls after the cancellation's turn are sends.
const isSend = (exec) =>
  mutant(exec, "windowCallsPlain") ? exec.cancelled : exec.cancelConsumed;

const startCall = (exec, io, op) => {
  op.kind = "call";
  if (!isSend(exec)) {
    op.idx = issueCmd(exec, io, { c: "call", op: op.op }, op.fiber);
  } else {
    op.send = true;
    // AMBIGUOUS: a compensation is any send issued after the first
    // cancellation's turn, from any fiber.
    op.compensation = exec.cancelled;
    const cmd = { c: "send", op: op.op, key: sendKey(exec, op) };
    op.key = cmd.key;
    op.idx = issueCmd(exec, io, cmd, op.fiber);
  }
  exec.byCmd[op.idx] = { role: "op", op: op.op };
  return true;
};

const issueAttach = (exec, io, op) => {
  const cmd = { c: "attach", op: op.op, target: op.key };
  op.attachIdx = issueCmd(exec, io, cmd, op.fiber);
  exec.byCmd[op.attachIdx] = { role: "attach", op: op.op };
};

// ---- awaiting (await and Effect.race) ----

// AMBIGUOUS: `race` is read as Effect.race, which returns the first
// success; a failure waits for the other side. When both are already
// done, the left one wins.
const awaitOps = (exec, io, fiber, names) => {
  const ops = names.map((name) => exec.ops[name]);
  if (ops.some((op) => !op || op.status === "released")) {
    recordViolation(exec, io, "other");
    fiber.unwind = failure("defect", "awaitReleased");
    return true;
  }
  const winner = ops.find((op) => op.status === "done" && isOk(op.result));
  if (winner) return winRace(exec, io, fiber, ops, winner);
  const failed = ops.filter((op) => op.status === "done");
  if (failed.length === ops.length) {
    fiber.unwind = failure("terminal", errorOf(failed[0]));
    return true;
  }
  fiber.status = "blocked";
  fiber.wait = { ops: names, failed: failed.map((op) => op.op) };
  return false;
};

const winRace = (exec, io, fiber, ops, winner) => {
  const losers = ops.filter((op) => op !== winner && op.status === "pending");
  if (losers.length > 0) {
    io.emit({ t: "interrupt", fiber: fiber.id, cause: "race" });
  }
  for (const op of losers) releaseOp(exec, io, op, "race");
  return true;
};

const onDelivered = (exec, io, fiber, op) => {
  const wait = fiber.wait;
  if (isOk(op.result)) {
    const ops = wait.ops.map((name) => exec.ops[name]);
    winRace(exec, io, fiber, ops, op);
    makeReady(exec, fiber);
    return;
  }
  wait.failed.push(op.op);
  if (wait.failed.length < wait.ops.length) return;
  fiber.resume = { fail: errorOf(exec.ops[wait.failed[0]]) };
  makeReady(exec, fiber);
};

const deliver = (exec, io, op, value) => {
  op.status = "done";
  op.result = value;
  io.emit({ t: "deliver", fiber: op.fiber, op: op.op, value });
  const fiber = exec.fibers[op.fiber];
  if (fiber.wait && fiber.wait.ops.includes(op.op)) {
    onDelivered(exec, io, fiber, op);
  }
};

// ---- the cause queue and turns (§3, §4, C19, M1) ----

const placeCancel = (exec, cause) => {
  const sampleOwned = exec.turnCause && exec.sampleIdx !== null;
  if (mutant(exec, "sampleToCancel") && sampleOwned) {
    exec.causes.unshift(exec.turnCause);
    exec.turnCause = cause;
    return;
  }
  if (mutant(exec, "cancelOvertakes")) exec.causes.unshift(cause);
  else exec.causes.push(cause);
};

const enqueue = (exec, cause) => {
  exec.causeSeq += 1;
  cause.seq = exec.causeSeq;
  if (cause.kind === "cancel") placeCancel(exec, cause);
  else exec.causes.push(cause);
};

const markActed = (exec, cause) => {
  if (cause.seq !== undefined) exec.acted[cause.seq] = true;
};

const fiberStopped = (exec, cause) =>
  cause.kind === "result" && exec.ops[cause.op].status !== "pending";

// AMBIGUOUS: the turn event is emitted when the turn takes its cause and
// issues its sample, not when the sample is applied.
const takeHead = (exec, io) => {
  const cause = exec.causes.shift();
  if (fiberStopped(exec, cause) && !mutant(exec, "noM1")) {
    markActed(exec, cause);
    return;
  }
  exec.turnCause = cause;
  // Only sampleToCancel puts the first turn's cause back in the queue.
  io.emit(cause.kind === "first"
    ? { t: "turn", cause: "first" }
    : { t: "turn", cause: "journal", entryIdx: cause.entryIdx });
  issueSample(exec, io);
};

// §4: L := max(L, s), then a delivered link credits its anchor plus d.
const credit = (exec, op, reading, before) => {
  if (mutant(exec, "rev5Credit")) {
    exec.L = Math.max(before + op.linkMs, reading);
  } else if (mutant(exec, "deliveryAnchor")) {
    exec.L = exec.L + op.linkMs;
  } else {
    exec.L = Math.max(exec.L, op.anchor + op.linkMs);
  }
};

// AMBIGUOUS: an intermediate link's turn delivers nothing to the fiber;
// it credits the link and issues the next one.
const actOnResult = (exec, io, cause, reading, before) => {
  const op = exec.ops[cause.op];
  if (op.status !== "pending") return;
  if (op.kind !== "sleep") return deliver(exec, io, op, cause.value);
  credit(exec, op, reading, before);
  if (op.links.length > 0) return issueLink(exec, io, op);
  deliver(exec, io, op, cause.value);
};

// §5: the first cancellation's turn interrupts the root; later ones are
// absorbed after taking their sample.
// Only sampleToCancel reaches a cancel before the root starts; the root
// is then interrupted before its first step.
const actOnCancel = (exec, io) => {
  if (exec.cancelled) return;
  exec.cancelled = true;
  if (exec.fibers.f0) interruptFiber(exec, io, exec.fibers.f0, "cancel");
};

const actOnCause = (exec, io, cause, reading, before) => {
  if (cause.kind === "first") spawnFiber(exec, io, "f0", null);
  if (cause.kind === "result") actOnResult(exec, io, cause, reading, before);
  if (cause.kind === "cancel") actOnCancel(exec, io);
};

const applySample = (exec, io, entry) => {
  const reading = entry.value.ok;
  const before = exec.L;
  exec.L = before === null ? reading : Math.max(before, reading);
  exec.sampleIdx = null;
  io.emit({ t: "sample", cmdIdx: entry.of, reading });
  const cause = exec.turnCause;
  exec.turnCause = null;
  exec.inTurn = true;
  actOnCause(exec, io, cause, reading, before);
  markActed(exec, cause);
  runFibers(exec, io);
  runDeferred(exec, io);
  exec.inTurn = false;
  if (exec.L > MAX_SAFE) recordViolation(exec, io, "overflow");
};

// ---- consuming the race's winner (§3) ----

const consumeResult = (exec, io, op, entry) => {
  op.consumed = true;
  delete exec.unconsumed[entry.of];
  if (op.retained || op.dropped) {
    op.retained = false; // C21: delivered to no fiber, no turn, no sample
    return;
  }
  if (op.status !== "pending" || exec.closing) return; // A33, §8
  const cause = { kind: "result", op: op.op, value: entry.value };
  enqueue(exec, { ...cause, entryIdx: entry.idx });
};

const consumeDeadline = (exec, io, op) => {
  op.deadlineConsumed = true;
  if (!op.consumed) abortRun(exec, io, op, "deadline"); // C23
};

// §3, M3, M10: an id lets the executor cancel the call or attach.
const consumeId = (exec, io, op) => {
  op.idArrived = true;
  if (op.mustCancel) return cancelCallOp(exec, io, op);
  const live = op.status === "pending" && !op.attachRetired;
  if (op.send && live && !exec.closing) issueAttach(exec, io, op);
};

// C22, withdrawn: re-attach every pending attach after a cancel signal.
const reattach = (exec, io) => {
  for (const op of Object.values(exec.ops)) {
    const pending = op.send && op.attachIdx !== null && !op.consumed;
    if (!pending || op.status !== "pending") continue;
    exec.byCmd[op.attachIdx] = { role: "retired" };
    issueAttach(exec, io, op);
  }
};

const consumeCancel = (exec, io, entry) => {
  exec.cancelConsumed = true;
  if (mutant(exec, "reattachOnCancel")) reattach(exec, io);
  // C30: after the root's exit a signal is absorbed.
  if (exec.rootExit || exec.closing) {
    exec.lateCancel = true;
    return;
  }
  enqueue(exec, { kind: "cancel", entryIdx: entry.idx });
};

// C25, M11: during the freeze only deadlines are acted on; every other
// entry leaves the race and waits for the next attempt.
const consumeFrozen = (exec, io, entry) => {
  if (entry.e === "cancel") return;
  const role = exec.byCmd[entry.of];
  const isResult = entry.value.invocationId === undefined;
  if (role && role.role === "deadline" && isResult) {
    return consumeDeadline(exec, io, exec.ops[role.op]);
  }
  exec.gone[isResult ? `r:${entry.of}` : `i:${entry.of}`] = true;
};

const consumeRole = (exec, io, role, entry) => {
  if (role.role === "sample") return applySample(exec, io, entry);
  const op = exec.ops[role.op];
  if (role.role === "deadline") return consumeDeadline(exec, io, op);
  if (role.role === "op" || role.role === "attach") {
    consumeResult(exec, io, op, entry);
  }
};

/** The race resolved with `entry`. */
export const onConsume = (exec, io, entry) => {
  io.emit({ t: "consume", entryIdx: entry.idx, entry });
  exec.lastVisible = io.now();
  if (exec.over) return;
  if (exec.frozen) return consumeFrozen(exec, io, entry);
  if (entry.e === "cancel") return consumeCancel(exec, io, entry);
  const role = exec.byCmd[entry.of];
  if (!role) return;
  if (entry.value.invocationId !== undefined) {
    return consumeId(exec, io, exec.ops[role.op]);
  }
  consumeRole(exec, io, role, entry);
};

// ---- the wrapper (§7.1, C17, C24, M7) ----

/** The SDK called a run's wrapper (A10). */
export const onWrapperCalled = (exec, io, idx) => {
  const sample = exec.byCmd[idx]?.role === "sample";
  exec.wrappers[idx] = { state: "waiting", sample };
  lifecycle(exec, io, "wrapper", idx);
  // M7: a sample passes the gate without waiting, so its wrapper call and
  // its entry are one step unless the freeze (or gateHoldsSamples) holds it.
  const held = exec.frozen || mutant(exec, "gateHoldsSamples");
  if (sample && !held) passGate(exec, io, idx, exec.wrappers[idx]);
};

// The closure lifecycle events of HISTORY.md, samples named
// "sample:<cmdIdx>".
const lifecycle = (exec, io, t, idx, outcome) => {
  const op = exec.wrappers[idx].sample ? `sample:${idx}` : exec.byCmd[idx].op;
  const event = { t, op, cmdIdx: idx };
  io.emit(outcome === undefined ? event : { ...event, outcome });
};

const outcomeOf = (value) => {
  if (value === "retryable") return "retryable";
  if (value.ok !== undefined) return "ok";
  return value.terminal === "aborted" ? "aborted" : "terminal";
};

const proposed = (value) =>
  value === "retryable" || value.ok !== undefined ? outcomeOf(value)
    : "terminal";

const gatePasses = (exec, wrapper) => {
  if (wrapper.sample && !mutant(exec, "gateHoldsSamples")) return true;
  if (mutant(exec, "noEntryGate")) return true;
  // M16: evaluated when the wrapper would release, over every cause
  // consumed so far, including those consumed while it waited.
  for (let seq = 1; seq <= exec.causeSeq; seq += 1) {
    if (!exec.acted[seq]) return false;
  }
  return true;
};

const returnToSdk = (exec, io, idx, value) => {
  const wrapper = exec.wrappers[idx];
  wrapper.state = "done";
  lifecycle(exec, io, "propose", idx, proposed(value));
  io.returnResult(idx, value);
  if (!wrapper.sample) exec.unconsumed[idx] = true;
};

const passGate = (exec, io, idx, wrapper) => {
  const refuse = exec.aborted[idx] && !mutant(exec, "noEntryCheck");
  if (wrapper.sample || !refuse) {
    wrapper.state = "entered";
    lifecycle(exec, io, "enter", idx);
    io.enterClosure(idx);
    return;
  }
  lifecycle(exec, io, "refuse", idx);
  io.refuseClosure(idx);
  returnToSdk(exec, io, idx, { terminal: "aborted" });
};

// The freeze holds samples too (C18). AMBIGUOUS: M7 lets samples pass
// the gate's wait, but C18 says the freeze starts no closure.
const tryGates = (exec, io) => {
  if (exec.frozen) return false;
  let changed = false;
  const waiting = Object.entries(exec.wrappers)
    .filter(([, w]) => w.state === "waiting")
    .sort(([a], [b]) => Number(a) - Number(b));
  for (const [idx, wrapper] of waiting) {
    if (!gatePasses(exec, wrapper)) continue;
    passGate(exec, io, Number(idx), wrapper);
    changed = true;
  }
  return changed;
};

// ---- settlement, classification and the freeze (§7.4, §7.5) ----

const classify = (exec, idx, raw) => {
  if (raw === "ok") return { ok: "ok" };
  if (raw === "terminal") return { terminal: "error" };
  if (raw === "interrupted" && exec.aborted[idx]) {
    return { terminal: "aborted" };
  }
  return "retryable";
};

const returnRetryable = (exec, io, idx) => {
  lifecycle(exec, io, "propose", idx, "retryable");
  io.returnRetryable(idx);
};

const hold = (exec, io, idx) => {
  exec.held.push(idx);
  if (mutant(exec, "noFreeze")) {
    exec.over = true;
    returnRetryable(exec, io, idx);
    return;
  }
  if (exec.frozen) return;
  exec.frozen = true;
  io.emit({ t: "freeze" });
};

/** A closure the wrapper entered has settled. */
export const onClosureSettled = (exec, io, idx, raw) => {
  const wrapper = exec.wrappers[idx];
  if (wrapper.sample) {
    lifecycle(exec, io, "settle", idx, "ok");
    return returnToSdk(exec, io, idx, { ok: raw.reading });
  }
  // handlerScheduler is M8 off: the run's Effect needs a turn to finish.
  if (mutant(exec, "handlerScheduler") && !exec.inTurn) {
    exec.deferred.push({ idx, raw });
    return;
  }
  wrapper.state = "settled";
  const value = classify(exec, idx, raw);
  lifecycle(exec, io, "settle", idx, outcomeOf(value));
  if (value === "retryable") return hold(exec, io, idx);
  if (exec.frozen) return exec.heldOk.push({ idx, value });
  returnToSdk(exec, io, idx, value);
};

const runDeferred = (exec, io) => {
  const pending = exec.deferred;
  exec.deferred = [];
  for (const { idx, raw } of pending) onClosureSettled(exec, io, idx, raw);
};

const executing = (exec) =>
  Object.values(exec.wrappers).filter((w) => w.state === "entered");

// M2: journaled outcomes first, then retryable failures in issue order;
// retryableFirst is M2 off.
const endFreeze = (exec, io) => {
  const byIssue = (a, b) => a - b;
  const okFirst = () => {
    for (const { idx, value } of exec.heldOk) returnToSdk(exec, io, idx, value);
  };
  if (!mutant(exec, "retryableFirst")) okFirst();
  exec.over = true;
  returnRetryable(exec, io, [...exec.held].sort(byIssue)[0]);
  if (mutant(exec, "retryableFirst")) okFirst();
  return true;
};

const freezeProgress = (exec, io) =>
  executing(exec).length === 0 ? endFreeze(exec, io) : false;

// ---- violations, exit and closing (§8, §9, X6) ----

const recordViolation = (exec, io, kind) => {
  exec.violations.push(kind);
  io.emit({ t: "violation", kind });
  latchClosing(exec);
};

const rootOutcome = (exec, exit) => {
  const details = exit.errors.map((e) => e.detail).join(",");
  const withDetail = (kind) =>
    details ? { kind, detail: details } : { kind };
  const has = (kind) => exit.errors.some((e) => e.kind === kind);
  if (has("defect")) return withDetail("defect");
  if (exit.interrupt === "cancel") return withDetail("cancelled");
  if (exit.interrupt) return withDetail("defect");
  if (has("terminal")) return withDetail("terminal");
  // AMBIGUOUS: HISTORY.md's Outcome has no retryable kind; a root that
  // fails retryably reports kind "retryable" in rootExit, and its attempt
  // ends "retry" with no Output.
  if (exit.errors.length > 0) return withDetail("retryable");
  return { kind: "success" };
};

const dropCauses = (exec) => {
  for (const cause of exec.causes) {
    if (cause.kind === "cancel") exec.lateCancel = true;
    markActed(exec, cause);
  }
  exec.causes = [];
};

const rootExited = (exec, io, exit) => {
  exec.rootExit = exit;
  io.emit({ t: "rootExit", outcome: rootOutcome(exec, exit) });
  dropCauses(exec);
  latchClosing(exec);
};

// X6 with C13: interrupt every live fiber and cancel its calls.
// X6.1: the root's exit or a violation latches closing at once: no
// delivery, no durable start, no new turn from the cause queue. Closing's
// own steps (interrupting live fibers) are a turn of their own, started
// from progress, so the executor first learns of every completion the
// latching turn caused (a settled promise's callbacks run before anything
// scheduled later), and no closing step runs while a failure is held
// (§7.4): a frozen attempt ends with the retry and the next one closes.
const latchClosing = (exec) => {
  exec.closing = true;
};

const startClosing = (exec, io) => {
  exec.closingTurn = true;
  io.emit({ t: "turn", cause: "local" });
  dropCauses(exec);
  for (const fiber of Object.values(exec.fibers)) {
    interruptFiber(exec, io, fiber, "closing");
  }
  runFibers(exec, io);
};

// C20, §7.7: ids for every cancel, no executing closure, every settled
// run's result consumed. noClosingAckWait drops the third.
// M14: and every run in the retained set has had its result consumed, so
// an unstarted retained run is started, refused by the wrapper's check,
// and its terminal abort journaled before Output (§7.2, S17, S20).
// Under noClosingAckWait a retained run whose result was already returned
// to the SDK is not waited for, or M14 would cover C20 and the mutant
// would change nothing.
const retainedPending = (exec) => {
  const skipAck = mutant(exec, "noClosingAckWait");
  return Object.values(exec.ops).some((op) =>
    op.retained && !(skipAck && exec.unconsumed[op.idx])); // M14
};

const closingWaits = (exec) => {
  const ids = Object.values(exec.ops).some((op) =>
    op.mustCancel && !op.cancelIssued);
  const acks = !mutant(exec, "noClosingAckWait") &&
    Object.keys(exec.unconsumed).length > 0;
  return ids || executing(exec).length > 0 || acks ||
    retainedPending(exec) ||
    Object.values(exec.wrappers).some((w) => w.state === "waiting");
};

const finalOutcome = (exec) => {
  const live = Object.values(exec.fibers).some((f) => f.status !== "done");
  if (exec.violations.length > 0 || live || !exec.rootExit) {
    return { kind: "defect", detail: exec.violations.join(",") || "live" };
  }
  const late = mutant(exec, "lateCancelReports409") && exec.lateCancel;
  return late ? { kind: "cancelled" } : rootOutcome(exec, exec.rootExit);
};

const closingProgress = (exec, io) => {
  if (!exec.closingTurn) {
    startClosing(exec, io);
    return true;
  }
  if (closingWaits(exec)) return false;
  const outcome = finalOutcome(exec);
  exec.over = true;
  if (outcome.kind === "retryable") io.failRetryable();
  else io.writeOutput(outcome);
  return true;
};

// S6: a handler blocked with nothing pending.
const blocked = (exec) =>
  !exec.rootExit && exec.causes.length === 0 && exec.turnCause === null &&
  exec.runQueue.length === 0 && raceMembers(exec) === null;

/** One deterministic step of the executor, if any is due. */
export const progress = (exec, io) => {
  if (exec.over) return false;
  if (tryGates(exec, io)) return true;
  if (exec.frozen) return freezeProgress(exec, io);
  if (exec.closing) return closingProgress(exec, io);
  if (exec.causes.length > 0 && exec.sampleIdx === null) {
    takeHead(exec, io);
    return true;
  }
  if (!blocked(exec)) return false;
  recordViolation(exec, io, "blocked");
  return true;
};

/** Restate's abort timeout: abort every executing run (C7), then the
 * executor closes after the cut, outside the attempt's trace. */
export const onEnded = (exec, io) => {
  exec.over = true;
  for (const [idx, wrapper] of Object.entries(exec.wrappers)) {
    if (wrapper.state !== "entered" || wrapper.sample) continue;
    abortRun(exec, io, exec.ops[exec.byCmd[idx].op], "ended");
  }
};

// ---- warnings (§12, C11, C16) ----

const executingAborted = (exec) =>
  Object.entries(exec.wrappers)
    .filter(([idx, w]) => w.state === "entered" && exec.aborted[idx])
    .map(([idx]) => Number(idx));

const holdsUp = (exec, abortedIdx) => {
  const mine = new Set(abortedIdx.flatMap((idx) => {
    const op = exec.ops[exec.byCmd[idx].op];
    return [`r:${idx}`, `r:${op.deadlineIdx}`];
  }));
  if (exec.frozen) return executing(exec).length > abortedIdx.length;
  if (exec.closing) {
    const others = { ...exec.unconsumed };
    for (const idx of abortedIdx) delete others[idx];
    const retainedOther = Object.values(exec.ops).some((op) =>
      op.retained && !abortedIdx.includes(op.idx));
    return Object.keys(others).length > 0 || retainedOther ||
      Object.values(exec.ops).some((op) => op.mustCancel && !op.cancelIssued);
  }
  if (exec.causes.length > 0 || exec.turnCause) return true;
  return (raceMembers(exec) ?? []).some((key) => !mine.has(key));
};

const opNames = (exec, indices) =>
  indices.map((idx) => exec.byCmd[idx].op).sort();

/** C16: warn once per attempt when aborted runs alone hold it up. */
export const checkWarnings = (exec, io) => {
  if (exec.warned1 || exec.over) return;
  const aborted = executingAborted(exec);
  if (aborted.length === 0 || holdsUp(exec, aborted)) return;
  exec.warned1 = true;
  const runs = opNames(exec, aborted);
  io.emit({ t: "warn", which: 1, runs, tick: io.now() });
};

/** C11: the executor's timer; warn once per run one inactivity timeout
 * after the later of its abort and the last exchange it saw.
 * AMBIGUOUS: time has tick resolution, the timer runs on each tick, and a
 * settlement is never at "the same moment" as a tick, so §12's tie rule
 * cannot arise. The last exchange the executor sees is its last race
 * consumption or issued command. */
export const onTick = (exec, io) => {
  if (exec.over) return;
  for (const idx of executingAborted(exec)) {
    const due = Math.max(exec.abortTime[idx], exec.lastVisible) +
      exec.cfg.inactivity;
    if (io.now() < due || exec.warned2[idx]) continue;
    exec.warned2[idx] = true;
    const runs = opNames(exec, [idx]);
    io.emit({ t: "warn", which: 2, runs, tick: io.now() });
  }
  checkWarnings(exec, io);
};
