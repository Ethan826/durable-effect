// rules/statements.mjs: executing statements, and starting durable
// operations (runs, sleeps as chains of links, calls and sends).

import { LINK_MAX, issueCmd, mutant } from "./base.mjs";
import { NO_ERRORS, errorOf, failure, spawnFiber } from "./fibers.mjs";
import { awaitOps } from "./turns.mjs";
import { recordViolation } from "./closing.mjs";

// ---- statements ----

const pushBlock = (fiber, kind, body, extra) => {
  fiber.frames.push({ k: kind, ...extra });
  fiber.frames.push({ k: "block", stmts: body, i: 0 });
};

export const execStmt = (exec, io, fiber, stmt) => {
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
    // hostTime, a control mutant: the executor reads the host clock.
    const L = mutant(exec, "hostTime") ? exec.L + io.now() : exec.L;
    io.emit({ t: "clock", fiber: fiber.id, L });
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
export const issueLink = (exec, io, op) => {
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

export const issueAttach = (exec, io, op) => {
  const cmd = { c: "attach", op: op.op, target: op.key };
  op.attachIdx = issueCmd(exec, io, cmd, op.fiber);
  exec.byCmd[op.attachIdx] = { role: "attach", op: op.op };
};
