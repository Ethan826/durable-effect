import { Effect, Scheduler } from "effect";
import type { Durable } from "../src/adapter/Durable.ts";
import type { AdapterRuntime } from "../src/adapter/Interface.ts";
import type { AnyFiber } from "../src/adapter/State.ts";

/**
 * Operations run in the current task, and the most in any task. Effect
 * counts each run loop's operations in the fiber's `currentOpCount`, which
 * it resets when a loop starts and leaves alone when the loop ends
 * (internal/effect.ts:675-735). So a loop's final count is exact,
 * inline steps after its last scheduler check included (:764-769).
 */
export interface OpCount {
  current: number;
  max: number;
  /** Fibers whose `runLoop` the counter wraps. */
  readonly wrapped: WeakSet<AnyFiber>;
  /** Fibers in a loop that began before the counter wrapped them. */
  readonly early: Set<AnyFiber>;
}

/** Adds an early loop's final count, once, if the fiber is in one. */
const settle = (count: OpCount, fiber: AnyFiber) => {
  if (count.early.delete(fiber)) count.current += fiber.currentOpCount;
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
      count.current += fiber.currentOpCount;
    }
  };
  Object.defineProperty(fiber, "runLoop", { value: counting });
};

/**
 * The first time a fiber is seen: its current loop began before the
 * counter could wrap it, so the loop counts whole when it ends, from its
 * first operation, whatever ran before the counter was installed.
 */
const observe = (count: OpCount, fiber: AnyFiber) => {
  if (count.wrapped.has(fiber)) return;
  count.wrapped.add(fiber);
  count.early.add(fiber);
  wrapRunLoop(count, fiber);
};

const counting = (inner: Scheduler.Scheduler, count: OpCount) => ({
  executionMode: inner.executionMode,
  makeDispatcher: () => inner.makeDispatcher(),
  shouldYield: (fiber: AnyFiber) => {
    observe(count, fiber);
    return inner.shouldYield(fiber);
  },
}) satisfies Scheduler.Scheduler;

/** The program, with every fiber's operations counted (I9). */
export const counted = <A, E>(
  effect: Effect.Effect<A, E, Durable>,
  count: OpCount,
) => Effect.withFiber((fiber) =>
  Effect.provideService(effect, Scheduler.Scheduler,
    counting(fiber.getRef(Scheduler.Scheduler), count))
);

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
export const freshCount = (): OpCount =>
  ({ current: 0, max: 0, wrapped: new WeakSet(), early: new Set() });
