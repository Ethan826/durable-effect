// rules/base.mjs: the executor's constants, the mutant test,
// createExecutor, issuing commands (§6's count), the race's members and
// aborts. It imports nothing.

export const MAX_SAFE = 2 ** 53 - 1;
const LINK_MAX = 2; // step 7's maximum link length, standing in for 2^31-1
export { LINK_MAX };

export const mutant = (exec, name) => exec.cfg.mutant === name;

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

export const issueCmd = (exec, io, cmd, fiber) => {
  const idx = io.issue(cmd);
  if (cmd.c !== "cancelCall") exec.opCount += 1;
  io.emit({ t: "issue", fiber, cmdIdx: idx, cmd });
  exec.lastVisible = io.now();
  return idx;
};

export const issueSample = (exec, io) => {
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

export const abortRun = (exec, io, op, cause) => {
  if (exec.aborted[op.idx]) return;
  exec.aborted[op.idx] = true;
  exec.abortTime[op.idx] = io.now();
  io.emit({ t: "abort", op: op.op, cause });
  io.abortSignal(op.idx);
};

export const cancelCallOp = (exec, io, op) => {
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
export const releaseOp = (exec, io, op, cause) => {
  if (op.status !== "pending") return;
  op.status = "released";
  io.emit({ t: "release", fiber: op.fiber, op: op.op, cause });
  if (op.kind === "run") releaseRun(exec, io, op);
  if (op.kind === "call") releaseCall(exec, io, op);
};
