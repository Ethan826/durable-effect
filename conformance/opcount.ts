import { Effect, Fiber, Scheduler } from "effect";
import type { Durable } from "../src/adapter/Durable.ts";
import type { AdapterRuntime, Host } from "../src/adapter/Interface.ts";
import type { AnyFiber } from "../src/adapter/State.ts";

/**
 * Operations counted for I9. An operation is one increment of a fiber's
 * `currentOpCount`, which Effect resets when a run loop starts and leaves
 * alone when the loop ends (internal/effect.ts:685, :693, :765). So a
 * loop's final count is exact, inline steps after its last scheduler check
 * included. `current` is this task's sum, `max` the most in any task and
 * `maxLoop` the most in any one run loop. `misregistered` counts fibers the
 * adapter registered after their first operation or with frames on their
 * stack.
 */
export interface OpCount {
  current: number;
  max: number;
  maxLoop: number;
  misregistered: number;
  /** Fibers whose `runLoop` the counter wraps. */
  readonly wrapped: WeakSet<AnyFiber>;
  /** Fibers in a loop that began before the counter wrapped them. */
  readonly early: Set<AnyFiber>;
}

/** Adds one ended run loop's final count. */
const addLoop = (count: OpCount, fiber: AnyFiber) => {
  count.current += fiber.currentOpCount;
  count.maxLoop = Math.max(count.maxLoop, fiber.currentOpCount);
};

/** Adds an early loop's final count, once, if the fiber is in one. */
const settle = (count: OpCount, fiber: AnyFiber) => {
  if (count.early.delete(fiber)) addLoop(count, fiber);
};

/**
 * Wraps the fiber's own `runLoop`, which Effect calls through the fiber
 * (:637), so every later loop adds its final count when it returns.
 */
const wrapRunLoop = (count: OpCount, fiber: AnyFiber) => {
  const original: unknown = Reflect.get(fiber, "runLoop");
  if (typeof original !== "function") return;
  const counting = (...args: unknown[]): unknown => {
    settle(count, fiber);
    try {
      return Reflect.apply(original, fiber, args);
    } finally {
      addLoop(count, fiber);
    }
  };
  Object.defineProperty(fiber, "runLoop", { value: counting });
};

/** Starts counting a fiber that is in its first counted run loop. */
const admit = (count: OpCount, fiber: AnyFiber) => {
  count.wrapped.add(fiber);
  count.early.add(fiber);
  wrapRunLoop(count, fiber);
};

/** The number of continuation frames on a fiber's stack (:743-757). */
const framesOf = (fiber: AnyFiber): number => {
  const stack: unknown = Reflect.get(fiber, "_stack");
  return Array.isArray(stack) ? stack.length : 0;
};

/**
 * The first time a fiber is seen: its current loop began before the
 * counter could wrap it, so the loop counts whole when it ends.
 */
const observe = (count: OpCount, fiber: AnyFiber) => {
  if (!count.wrapped.has(fiber)) admit(count, fiber);
};

/**
 * Whether a fiber registers as I9's restriction requires: in its first
 * operation, where Effect has reset `currentOpCount` (:528, :685) and
 * counted one (:693), with nothing on its stack. Registered later, with
 * frames, a registration interrupt leaves `yielding` set for the rest of
 * the loop (:698-723), so the scheduler could no longer stop it.
 */
const registersCleanly = (fiber: AnyFiber | undefined) =>
  fiber !== undefined && fiber.currentOpCount === 1 && framesOf(fiber) === 0;

/**
 * The host, with each registration checked against I9's restriction. The
 * adapter registers a fiber from inside that fiber's run loop, so the
 * fiber registering is the current one. The root goes through it too.
 */
export const checkedRegistration = (host: Host, count: OpCount): Host => ({
  ...host,
  register: (fiber) => {
    if (!registersCleanly(Fiber.getCurrent())) count.misregistered += 1;
    return host.register(fiber);
  },
});

const counting = (inner: Scheduler.Scheduler, count: OpCount) => ({
  executionMode: inner.executionMode,
  makeDispatcher: () => inner.makeDispatcher(),
  shouldYield: (fiber: AnyFiber) => {
    observe(count, fiber);
    return inner.shouldYield(fiber);
  },
}) satisfies Scheduler.Scheduler;

/**
 * The program, with every fiber's operations counted (I9). The root met
 * the adapter's scheduler at its first operation, before this runs, so it
 * is admitted here and its first loop still counts from its start.
 */
export const counted = <A, E>(
  effect: Effect.Effect<A, E, Durable>,
  count: OpCount,
) => Effect.withFiber((root) => {
  admit(count, root);
  return Effect.provideService(effect, Scheduler.Scheduler,
    counting(root.getRef(Scheduler.Scheduler), count));
});

/** The runtime, with the operation count reset before each task. */
export const perTask = (
  runtime: AdapterRuntime,
  count: OpCount,
): AdapterRuntime => ({
  runTask: (task) => {
    count.current = 0;
    runtime.runTask(task);
    // A loop never outlasts its task, so every early loop has ended.
    count.early.forEach((fiber) => settle(count, fiber));
    count.max = Math.max(count.max, count.current);
  },
});

/** A count with nothing counted yet. */
export const freshCount = (): OpCount => ({
  current: 0,
  max: 0,
  maxLoop: 0,
  misregistered: 0,
  wrapped: new WeakSet(),
  early: new Set(),
});
