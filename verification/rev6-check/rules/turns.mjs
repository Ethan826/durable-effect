// rules/turns.mjs: awaiting (await and Effect.race), and the cause queue
// and the turns it starts.

import { MAX_SAFE, issueSample, mutant, releaseOp } from "./base.mjs";
import { errorOf, failure, interruptFiber, isOk } from "./fibers.mjs";
import { makeReady, runFibers, spawnFiber } from "./fibers.mjs";
import { issueLink } from "./statements.mjs";
import { recordViolation, runDeferred } from "./closing.mjs";

// ---- awaiting (await and Effect.race) ----

// AMBIGUOUS: `race` is read as Effect.race, which returns the first
// success; a failure waits for the other side. When both are already
// done, the left one wins.
export const awaitOps = (exec, io, fiber, names) => {
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

export const enqueue = (exec, cause) => {
  exec.causeSeq += 1;
  cause.seq = exec.causeSeq;
  if (cause.kind === "cancel") placeCancel(exec, cause);
  else exec.causes.push(cause);
};

export const markActed = (exec, cause) => {
  if (cause.seq !== undefined) exec.acted[cause.seq] = true;
};

const fiberStopped = (exec, cause) =>
  cause.kind === "result" && exec.ops[cause.op].status !== "pending";

// AMBIGUOUS: the turn event is emitted when the turn takes its cause and
// issues its sample, not when the sample is applied.
export const takeHead = (exec, io) => {
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

export const applySample = (exec, io, entry) => {
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
