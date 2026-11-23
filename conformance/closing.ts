import { Clock, Effect } from "effect";
import type { Journal } from "./deliveries.ts";
import type { Program } from "./grammar.ts";
import type { Handler } from "./lifecycle.ts";

// I8's pinned cases, from #37's table: "an uninterruptible detached fork
// and a concurrent `forEach` in a closing finalizer". In each a fiber
// first runs during closing while Effect has it masked, which takes the
// starts-masked branch of the adapter's registration (Fibers.ts:31-53).
// The grammar cannot reach either (grammar.ts:59: a `Fork` has no mask of
// its own, and 5,000 programs registered none masked during closing), so
// they are written directly in Effect, as I9's pinned cases are.

/** A loop of `count` steps, one Effect operation each. */
const loop = (count: number) =>
  Effect.suspend(() => {
    const done = { steps: 0 };
    return Effect.whileLoop({
      while: () => done.steps < count,
      body: () => Effect.sync(() => done.steps++),
      step: () => {},
    });
  });

/**
 * A: the root forks a detached fiber that is uninterruptible from its
 * first step and exits at once, so the fork first runs during closing.
 * It reads the clock and yields before it ends.
 */
const maskedDetached: Handler = Effect.asVoid(Effect.forkDetach(
  Effect.andThen(Clock.currentTimeMillis, Effect.yieldNow),
  { uninterruptible: true },
));

/**
 * B: a detached fiber waits forever under a finalizer that runs a
 * concurrent `forEach`. Closing interrupts it; the finalizer runs masked,
 * and the `forEach` children it forks inherit the mask, so each first
 * runs during closing, masked.
 */
const closingForEach: Handler = Effect.andThen(
  Effect.forkDetach(Effect.ensuring(Effect.never, Effect.forEach(
    [1, 2, 2049], loop, { concurrency: "unbounded", discard: true },
  ))),
  Effect.yieldNow,
);

/** The pinned cases, by name. */
export const closingCases = { maskedDetached, closingForEach } as const;

/** No program for the shape counts, and one `Value` 0 for every run. */
export const closingSampled: readonly [Program, Journal] = [
  { root: [], forks: [] },
  { outcomes: [{ _tag: "Value", value: 0 }], cancelBefore: undefined },
];
