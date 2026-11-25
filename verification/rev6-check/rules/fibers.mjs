// rules/fibers.mjs: the fiber runtime, a stand-in for Effect's (fibers,
// masks, finalizers, structured concurrency).

import { releaseOp } from "./base.mjs";
import { execStmt } from "./statements.mjs";
import { rootExited } from "./closing.mjs";

// ---- the fiber runtime (stand-in for Effect; I4, I6, I8) ----

export const NO_ERRORS = { interrupt: null, errors: [] };

const combine = (first, second) => ({
  interrupt: first.interrupt || second.interrupt,
  errors: [...first.errors, ...second.errors],
});

export const failure = (kind, detail) => ({ interrupt: null,
  errors: [{ kind, detail }] });

export const isOk = (value) => value && value.ok !== undefined;

const errorOf = (op) => `${op.op}:${op.result.terminal ?? op.result.defect}`;
export { errorOf };

export const spawnFiber = (exec, io, id, parent) => {
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

export const makeReady = (exec, fiber) => {
  fiber.status = "ready";
  fiber.wait = null;
  if (!exec.runQueue.includes(fiber.id)) exec.runQueue.push(fiber.id);
};

/** Interrupt a fiber. A masked fiber keeps its await (I4).
 * AMBIGUOUS: only the awaited operations are released here; the fiber's
 * other started operations are released when it exits (a started
 * operation behaves as a forked child of the fiber). A fiber that has
 * finished its body and is joining its children is not interrupted. */
export const interruptFiber = (exec, io, fiber, cause) => {
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
export const runFibers = (exec, io) => {
  while (exec.runQueue.length > 0 && !exec.over) {
    const fiber = exec.fibers[exec.runQueue.shift()];
    if (fiber.status === "ready") stepFiber(exec, io, fiber);
  }
};
