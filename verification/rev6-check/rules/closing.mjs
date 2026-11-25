// rules/closing.mjs: settlement, classification and the freeze, and
// violations, the root's exit and closing.

import { abortRun, mutant, raceMembers } from "./base.mjs";
import { interruptFiber, runFibers } from "./fibers.mjs";
import { markActed, takeHead } from "./turns.mjs";
import { lifecycle, outcomeOf, returnToSdk, tryGates } from "./consume.mjs";

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

export const runDeferred = (exec, io) => {
  const pending = exec.deferred;
  exec.deferred = [];
  for (const { idx, raw } of pending) onClosureSettled(exec, io, idx, raw);
};

export const executing = (exec) =>
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

export const recordViolation = (exec, io, kind) => {
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

export const rootExited = (exec, io, exit) => {
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
