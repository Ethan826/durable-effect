import { expect, test } from "bun:test";
import { Effect, Schema } from "effect";
import { TaskId } from "../../src/adapter/Interface.ts";
import type { Event } from "../../src/adapter/Interface.ts";
import { makeState } from "../../src/adapter/State.ts";
import type { AdapterState } from "../../src/adapter/State.ts";
import { deterministicScheduler } from "../../src/adapter/Scheduler.ts";
import type { Host } from "../../src/adapter/Interface.ts";

/** A host that keeps every emitted event and answers nothing else. */
const recordingHost = (events: Event[]): Host => ({
  emit: (event) => {
    events.push(event);
  },
  clock: () => 0,
  draw: () => 0,
  register: () => true,
  inSlice: () => true,
  foreign: () => {},
  noteGlobal: () => {},
});

/** The `Queue` event for a priority and a task number. */
const queue = (priority: number, task: number): Event => ({
  _tag: "Queue",
  priority,
  task: Schema.decodeSync(TaskId)(task),
});

/** Starts an effect under the deterministic scheduler. */
const start = (
  state: AdapterState,
  events: Event[],
  effect: Effect.Effect<void>,
) =>
  Effect.runFork(effect, {
    scheduler: deterministicScheduler(state, recordingHost(events)),
  });

/** Runs every queued task, as the host would on `RunQueued`. */
const drain = (state: AdapterState, events: Event[]) => {
  let seen = 0;
  while (seen < events.length) {
    const event = events[seen++];
    if (event?._tag === "Queue") state.tasks.get(event.task)?.();
  }
};

const steps = (count: number, ran?: number[]): Effect.Effect<void> =>
  count === 0
    ? Effect.void
    : Effect.flatMap(
        Effect.sync(() => ran?.push(count)),
        () => steps(count - 1, ran),
      );

test("yieldNow emits one Queue at priority 0", () => {
  const state = makeState();
  const events: Event[] = [];
  start(state, events, Effect.yieldNow);
  expect(events).toEqual([queue(0, 0)]);
});

test("yieldNowWith(1) emits Queue at priority 1", () => {
  const state = makeState();
  const events: Event[] = [];
  start(state, events, Effect.yieldNowWith(1));
  expect(events).toEqual([queue(1, 0)]);
});

test("a queued task resumes the fiber when run", () => {
  const state = makeState();
  const events: Event[] = [];
  let done = false;
  start(state, events, Effect.andThen(Effect.yieldNow, Effect.sync(() => {
    done = true;
  })));
  expect(done).toBe(false);
  drain(state, events);
  expect(done).toBe(true);
});

test("a short loop emits no Queue", () => {
  const state = makeState();
  const events: Event[] = [];
  start(state, events, steps(100));
  expect(events).toEqual([]);
});

test("a long loop yields at the 2,048-operation budget", () => {
  const state = makeState();
  const events: Event[] = [];
  const ran: number[] = [];
  start(state, events, steps(3000, ran));
  expect(events.length).toBe(1);
  expect(ran.length).toBeGreaterThan(0);
  expect(ran.length).toBeLessThan(2048);
  expect(events[0]).toMatchObject({ _tag: "Queue", priority: 0 });
  drain(state, events);
  expect(ran.length).toBe(3000);
});

test("shouldYield calls the state's registration step", () => {
  const state = makeState();
  const seen: unknown[] = [];
  state.register = (fiber) => {
    seen.push(fiber);
    return false;
  };
  start(state, [], Effect.void);
  expect(seen.length).toBeGreaterThan(0);
});

test("shouldYield yields when registration answers true", () => {
  const state = makeState();
  const events: Event[] = [];
  state.register = () => true;
  start(state, events, Effect.void);
  expect(events[0]).toMatchObject({ _tag: "Queue", priority: 0 });
});

test("two adapters number their tasks independently", () => {
  const first = makeState();
  const second = makeState();
  const a: Event[] = [];
  const b: Event[] = [];
  start(first, a, Effect.yieldNow);
  start(first, a, Effect.yieldNow);
  start(second, b, Effect.yieldNow);
  expect(a).toEqual([queue(0, 0), queue(0, 1)]);
  expect(b).toEqual([queue(0, 0)]);
});
