import assert from "node:assert/strict";
import { test } from "node:test";
import { Effect, Fiber, Scheduler } from "effect";
import { makeAdapter } from "../src/adapter/Runtime.ts";
import { scriptedHost } from "./host.ts";
import { mutants } from "./mutants.ts";
import {
  checkedRegistration,
  counted,
  freshCount,
  perTask,
} from "./opcount.ts";

const journal = {
  outcomes: [{ _tag: "Value", value: 0 }],
  cancelBefore: undefined,
} as const;

/**
 * The operations of the root's last run loop, as Effect itself counts
 * them: `currentOpCount` when the root exits. When that loop is the whole
 * of the last task, the counter must see at least this many.
 */
const lastLoop = (body: Effect.Effect<unknown>) => {
  const seen = { final: 0, counted: 0 };
  const program = Effect.withFiber((fiber) => {
    fiber.addObserver(() => {
      seen.final = fiber.currentOpCount;
    });
    return Effect.andThen(Effect.yieldNow, body);
  });
  const host = scriptedHost(journal, { seed: 1 });
  const count = freshCount();
  host.run(perTask(makeAdapter(counted(program, count), 0, host), count));
  seen.counted = count.current;
  return seen;
};

const bodies: ReadonlyArray<Effect.Effect<unknown>> = [
  Effect.void,
  Effect.succeed(1),
  Effect.map(Effect.sync(() => 1), (value) => value + 1),
  Effect.forEach([1, 2, 3], (value) => Effect.succeed(value)),
];

// The last task resumes the root and runs it to its exit in one run loop.
// Operations after the loop's last scheduler check (internal/effect.ts
// :764-769) must count too, so the count is never below Effect's own.
test("a task's count is at least Effect's own count of its loop", () => {
  const short = bodies.map(lastLoop).filter((seen) =>
    seen.counted < seen.final
  );
  assert.deepEqual(short, []);
});

// A fiber's first run loop starts before the counter is installed; its
// operations before that still count.
test("counts the root's operations from the start of its first loop", () => {
  const seen = { start: 0 };
  const program = Effect.withFiber((fiber) => {
    seen.start = fiber.currentOpCount;
    return Effect.never;
  });
  const host = scriptedHost(journal, { seed: 1 });
  const count = freshCount();
  host.run(perTask(makeAdapter(counted(program, count), 0, host), count));
  assert.ok(seen.start > 0);
  assert.ok(count.max >= seen.start, `${count.max} < ${seen.start}`);
});

/** A loop of `steps` pure steps, each one Effect operation or more. */
const pureLoop = (steps: number) => Effect.suspend(() => {
  const done = { steps: 0 };
  return Effect.whileLoop({
    while: () => done.steps < steps,
    body: () => Effect.sync(() => done.steps++),
    step: () => {},
  });
});

/** The count after running `program` under `make`. */
const countOf = (
  program: Effect.Effect<unknown>,
  make: typeof makeAdapter = makeAdapter,
) => {
  const host = scriptedHost(journal, { seed: 1 });
  const count = freshCount();
  const checked = checkedRegistration(host, count);
  host.run(perTask(make(counted(program, count), 0, checked), count));
  return count;
};

// I9's main check: every run loop yields by 2,049 operations, B + 1,
// because succeedWith returns at multiples of 32 (:765, :843).
test("no run loop passes 2,049 operations; neverYields does", () => {
  const adapter = countOf(pureLoop(5000));
  const mutant = countOf(pureLoop(5000), mutants.neverYields.make);
  assert.ok(adapter.maxLoop <= 2049 && adapter.maxLoop >= 2000,
    `${adapter.maxLoop}`);
  assert.ok(mutant.maxLoop > 2049, `${mutant.maxLoop}`);
});

/**
 * A fiber forked under a scheduler of the program's own, which then
 * meets the adapter's scheduler inside `provideService`, with frames on
 * its stack: the registration condition the restriction rules out.
 */
const strayFork = Effect.withFiber((parent) => {
  const adapterSide = parent.getRef(Scheduler.Scheduler);
  const own = { ...adapterSide, shouldYield: () => false };
  const body = Effect.flatMap(
    Effect.provideService(pureLoop(3), Scheduler.Scheduler, adapterSide),
    () => pureLoop(3),
  );
  return Effect.provideService(
    Effect.flatMap(Effect.forkChild(body), Fiber.join),
    Scheduler.Scheduler,
    own,
  );
});

test("each fiber, the root too, registers at its first operation", () => {
  assert.equal(countOf(pureLoop(3)).misregistered, 0);
  assert.equal(countOf(strayFork).misregistered, 1);
});
