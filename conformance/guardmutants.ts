import { Effect, Scheduler } from "effect";
import type { Host } from "../src/adapter/Interface.ts";
import { makeAdapter } from "../src/adapter/Runtime.ts";
import type { AnyFiber } from "../src/adapter/State.ts";
import type { Variant } from "./mutants.ts";

// I3's mutants, #37's table: a callback resumed with
// `PreventSchedulerYield` set; an adapter that runs the resumed
// continuation; one without the `interruptUnsafe` wrapper; and a wrapper
// that records the violation and then forwards the call.

type Wrap = (inner: Scheduler.Scheduler, host: Host) => Scheduler.Scheduler;

/**
 * The adapter, with every fiber of the program under the scheduler `wrap`
 * makes from the adapter's own. The root's first operation runs before
 * the program, so the root alone keeps the adapter's scheduler there.
 */
const rescheduled = (wrap: Wrap): Variant => (program, seed, host) =>
  makeAdapter(Effect.withFiber((fiber) =>
    Effect.provideService(program, Scheduler.Scheduler,
      wrap(fiber.getRef(Scheduler.Scheduler), host))
  ), seed, host);

/** The program runs with `PreventSchedulerYield`, so no guard is asked. */
const preventYield: Variant = (program, seed, host) =>
  makeAdapter(
    Effect.provideService(program, Scheduler.PreventSchedulerYield, true),
    seed,
    host,
  );

/** The guard is asked, but outside a slice the fiber does not yield. */
const runsContinuation = rescheduled((inner, host) => ({
  executionMode: inner.executionMode,
  makeDispatcher: () => inner.makeDispatcher(),
  shouldYield: (fiber) => inner.shouldYield(fiber) && host.inSlice(),
}));

type Interrupt = AnyFiber["interruptUnsafe"];

/** Effect's own `interruptUnsafe` for a fiber, from its prototype. */
const originalOf = (fiber: AnyFiber): Interrupt => {
  const method: unknown = Reflect.get(Object.getPrototypeOf(fiber),
    "interruptUnsafe");
  return (...args) => {
    if (typeof method === "function") Reflect.apply(method, fiber, args);
  };
};

/** What a fiber's `interruptUnsafe` becomes, from the adapter's guard. */
type Rewire = (guard: Interrupt, original: Interrupt, host: Host) => Interrupt;

const settable = { writable: true, configurable: true } as const;

/**
 * Lets the adapter install its guard on a fiber the first time it is
 * seen, then replaces it with `rewire`'s. The property is made changeable
 * first, since the adapter defines it read-only; on the root, seen too
 * late, the definition fails and the guard stays.
 */
const rewired = (rewire: Rewire) => rescheduled((inner, host) => {
  const seen = new WeakSet<AnyFiber>();
  return {
    executionMode: inner.executionMode,
    makeDispatcher: () => inner.makeDispatcher(),
    shouldYield: (fiber) => {
      if (seen.has(fiber)) return inner.shouldYield(fiber);
      seen.add(fiber);
      const original = originalOf(fiber);
      const open = Reflect.defineProperty(fiber, "interruptUnsafe",
        { value: original, ...settable });
      const answer = inner.shouldYield(fiber);
      const guard = fiber.interruptUnsafe;
      const value = rewire(guard, original, host);
      if (open) Reflect.defineProperty(fiber, "interruptUnsafe", { value });
      return answer;
    },
  };
});

/** No wrapper: a foreign interrupt reaches Effect, and is not reported. */
const withoutWrapper = rewired((_, original) => original);

/** The wrapper reports a foreign interrupt, then forwards it anyway. */
const recordsThenForwards = rewired((guard, original, host) =>
  (...args) => {
    guard(...args);
    if (!host.inSlice()) original(...args);
  });

/** I3's mutants, by name. */
export const guardMutants = {
  preventYield,
  runsContinuation,
  withoutWrapper,
  recordsThenForwards,
} as const;
