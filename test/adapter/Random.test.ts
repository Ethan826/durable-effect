import { expect, test } from "bun:test";
import { Brand, Effect, Random } from "effect";
import type { Durable } from "../../src/adapter/Durable.ts";
import type {
  AdapterRuntime,
  Event,
  FiberId,
  Host,
} from "../../src/adapter/Interface.ts";
import { makeAdapter } from "../../src/adapter/Runtime.ts";

// The expected values below are written out by hand from Effect 4.1.5's
// own layout (effect/src/Random.ts:611-627): a double is 21 bits of the
// first draw over 32 bits of the second, divided by 2^53, and an int is
// that double scaled onto the safe integers.

const fiberId = Brand.nominal<FiberId>();
const allBits = 2 ** 32 - 1;

/** A host that answers draws in order and logs who asked. */
const drawingHost = (
  events: Event[],
  askers: FiberId[],
  draws: number[],
): Host => ({
  emit: (event) => {
    events.push(event);
  },
  clock: () => 0,
  draw: (fiber) => {
    askers.push(fiber);
    return draws.shift() ?? 0;
  },
  register: () => false,
  inSlice: () => true,
  foreign: () => {},
  noteGlobal: () => {},
});

/** Runs every task the adapter has queued so far, and any they queue. */
const runQueued = (events: Event[], adapter: AdapterRuntime) => {
  for (let seen = 0; seen < events.length; seen++) {
    const entry = events[seen];
    if (entry?._tag === "Queue") {
      adapter.runTask({ _tag: "RunQueued", task: entry.task });
    }
  }
};

/** Runs the program and every task it queues; answers its value. */
const runDrawing = <A>(
  program: Effect.Effect<A, unknown, Durable>,
  draws: number[],
) => {
  const events: Event[] = [];
  const askers: FiberId[] = [];
  const kept: A[] = [];
  const keep = (value: A) => Effect.sync(() => kept.push(value));
  const host = drawingHost(events, askers, draws);
  const adapter = makeAdapter(Effect.tap(program, keep), 0, host);
  adapter.runTask({ _tag: "StartRoot" });
  runQueued(events, adapter);
  return { kept, askers };
};

const twoDoubles = Effect.all([Random.next, Random.next]);
const twoInts = Effect.all([Random.nextInt, Random.nextInt]);

test("a double is the low 21 bits of one draw over all 32 of the next", () => {
  const { kept, askers } = runDrawing(twoDoubles, [1, 0, 2 ** 21 + 3, 5]);
  expect(kept).toEqual([[2 ** -21, 3 * 2 ** -21 + 5 * 2 ** -53]]);
  expect(askers).toEqual([0, 0, 0, 0].map(fiberId));
});

test("the largest draws give the largest double below 1", () => {
  const { kept } = runDrawing(Random.next, [allBits, allBits]);
  expect(kept).toEqual([1 - 2 ** -53]);
});

test("an int scales the double onto the safe integers", () => {
  const { kept } = runDrawing(twoInts, [0, 0, 2 ** 20, 0]);
  expect(kept).toEqual([[Number.MIN_SAFE_INTEGER, 1]]);
});

test("the largest draws give the largest safe integer", () => {
  const { kept } = runDrawing(Random.nextInt, [allBits, allBits]);
  expect(kept).toEqual([Number.MAX_SAFE_INTEGER]);
});

test("two draws from two fibers ask with each fiber's id", () => {
  const { kept, askers } = runDrawing(
    Effect.all([Random.next, Random.next], { concurrency: "unbounded" }),
    [2 ** 19, 0, 2 ** 20, 0],
  );
  expect(askers).toEqual([1, 1, 2, 2].map(fiberId));
  expect(kept).toEqual([[0.25, 0.5]]);
});
