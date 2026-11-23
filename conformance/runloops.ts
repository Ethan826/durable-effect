import { Effect } from "effect";

// An oracle for S, I9's count of statement-fiber run loops in one task. It
// shares nothing with opcount.ts: it patches Effect's fiber prototype once
// per process, sees every run loop of every fiber, and never reads
// `currentOpCount`. A statement fiber (the root, a fork body, or the
// two-fiber deadlock's child) is one whose first run loop starts at the
// top of a task. Every helper fiber that `forEach`, `race`, `timeout` and
// `cached` make starts inside its parent's run loop (internal/effect.ts
// :5238, :1788, :4615).

/** S: the most statement-fiber run loops one task may run. */
export const maxStatementLoops = 24;

const state = {
  active: 0,
  current: 0,
  statement: new WeakSet<object>(),
  seen: new WeakSet<object>(),
};

const classify = (fiber: object) => {
  if (state.seen.has(fiber)) return;
  state.seen.add(fiber);
  if (state.active === 0) state.statement.add(fiber);
};

const counting: ProxyHandler<(...args: unknown[]) => unknown> = {
  apply: (target, fiber: object, args) => {
    classify(fiber);
    if (state.statement.has(fiber)) state.current += 1;
    state.active += 1;
    try {
      return Reflect.apply(target, fiber, args);
    } finally {
      state.active -= 1;
    }
  },
};

/** Wraps `runLoop` on the prototype every Effect fiber shares, once. */
const install = () => {
  const prototype: unknown = Object.getPrototypeOf(Effect.runFork(Effect.void));
  if (typeof prototype !== "object" || prototype === null) return;
  const original: unknown = Reflect.get(prototype, "runLoop");
  if (typeof original !== "function") return;
  Reflect.set(prototype, "runLoop", new Proxy(original, counting));
};

install();

/** Starts a task's count of statement-fiber run loops. */
export const beginTask = () => {
  state.current = 0;
  state.active = 0;
};

/** The statement-fiber run loops of the task just run. */
export const endTask = (): number => state.current;
