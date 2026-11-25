// rules/warnings.mjs: the two warnings about aborted runs (§12).

import { raceMembers } from "./base.mjs";
import { executing } from "./closing.mjs";

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
