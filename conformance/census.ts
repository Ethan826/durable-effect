import { Effect } from "effect";
import type { AnyFiber } from "../src/adapter/State.ts";

// An oracle for I5 and I8 that shares nothing with the adapter. At the
// first `beginRun` in a process it patches the run loop on the prototype
// every Effect fiber shares, and from then on sees every run loop of every
// fiber (internal/effect.ts :637). While a task is open it counts the
// loops that start and keeps each fiber that ran. It also tracks how many
// loops are running, which tells a fiber started inside another's loop
// from one a task started.

const state = {
  open: false,
  depth: 0,
  loops: 0,
  fibers: new Set<AnyFiber>(),
  started: { internal: 0, detached: 0, inlineWakes: 0 },
};

const isFiber = (value: object): value is AnyFiber =>
  "pollUnsafe" in value && "interruptUnsafe" in value;

/**
 * Sorts a fiber at its first loop: started inside another fiber's loop
 * (internal: `forEach`, `race`, `cached`, ...), or by a task with no
 * parent and not the first fiber, the root (detached). Effect clears
 * `_parent` when a fiber exits (:654-657), so it is read here.
 */
const sort = (fiber: AnyFiber) => {
  if (state.depth > 0) state.started.internal += 1;
  const orphan = Reflect.get(fiber, "_parent") === undefined;
  const root = state.fibers.size === 0;
  if (state.depth === 0 && orphan && !root) state.started.detached += 1;
};

/**
 * A later loop of a fiber already seen, started inside another fiber's
 * loop, is a wake within the task: a deferred or an exit resuming it.
 */
const noteLoop = (fiber: object) => {
  if (!state.open || !isFiber(fiber)) return;
  state.loops += 1;
  if (state.fibers.has(fiber)) {
    if (state.depth > 0) state.started.inlineWakes += 1;
    return;
  }
  sort(fiber);
  state.fibers.add(fiber);
};

const counting: ProxyHandler<(...args: unknown[]) => unknown> = {
  apply: (target, fiber: object, args) => {
    noteLoop(fiber);
    state.depth += 1;
    try {
      return Reflect.apply(target, fiber, args);
    } finally {
      state.depth -= 1;
    }
  },
};

const installed = { done: false };

/**
 * Wraps `runLoop` on the shared fiber prototype, once, at the first run.
 * Nothing is wrapped while the module is merely loaded.
 */
const install = () => {
  if (installed.done) return;
  installed.done = true;
  const prototype: unknown = Object.getPrototypeOf(Effect.runFork(Effect.void));
  if (typeof prototype !== "object" || prototype === null) return;
  const original: unknown = Reflect.get(prototype, "runLoop");
  if (typeof original !== "function") return;
  Reflect.set(prototype, "runLoop", new Proxy(original, counting));
};

/**
 * How many run loops are running now, the current one included. The first
 * call installs the census, so a caller outside a lifecycle run, such as
 * a mutant driven by the sequences, still gets a true depth from then on.
 */
export const loopDepth = (): number => {
  install();
  return state.depth;
};

/** Installs the census if needed and forgets every fiber seen. */
export const beginRun = () => {
  install();
  state.fibers = new Set();
  state.started = { internal: 0, detached: 0, inlineWakes: 0 };
};

/**
 * Runs `task` with the census open and answers how many run loops started
 * while it ran. Every fiber that ran is kept until the next `beginRun`.
 */
export const openTask = (task: () => void): number => {
  state.open = true;
  state.loops = 0;
  try {
    task();
  } finally {
    state.open = false;
  }
  return state.loops;
};

/** Since `beginRun`: internal and detached fibers, and inline wakes. */
export interface Started {
  readonly internal: number;
  readonly detached: number;
  readonly inlineWakes: number;
}

/** What the census sorted since `beginRun`. */
export const startedKinds = (): Started => ({ ...state.started });

/** The fibers that ran in a task since `beginRun`, in first-run order. */
export const fibersRun = (): ReadonlyArray<AnyFiber> => [...state.fibers];
