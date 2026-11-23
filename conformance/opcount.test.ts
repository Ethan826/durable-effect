import assert from "node:assert/strict";
import { test } from "node:test";
import { Effect } from "effect";
import { makeAdapter } from "../src/adapter/Runtime.ts";
import { scriptedHost } from "./host.ts";
import { counted, freshCount, perTask } from "./opcount.ts";

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
