// rules/consume.mjs: consuming the race's winner, and the run's wrapper
// with its entry gate.

import { abortRun, cancelCallOp, mutant } from "./base.mjs";
import { issueAttach } from "./statements.mjs";
import { applySample, enqueue } from "./turns.mjs";

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
export const lifecycle = (exec, io, t, idx, outcome) => {
  const op = exec.wrappers[idx].sample ? `sample:${idx}` : exec.byCmd[idx].op;
  const event = { t, op, cmdIdx: idx };
  io.emit(outcome === undefined ? event : { ...event, outcome });
};

export const outcomeOf = (value) => {
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

export const returnToSdk = (exec, io, idx, value) => {
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
export const tryGates = (exec, io) => {
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
