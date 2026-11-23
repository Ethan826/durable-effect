import { expect, test } from "bun:test";
import { Effect } from "effect";
import type { Host } from "../../src/adapter/Interface.ts";
import { registration } from "../../src/adapter/Fibers.ts";
import { makeState } from "../../src/adapter/State.ts";

// The adapter keeps only live fibers in its map, so an attempt that forks
// many short fibers does not hold every one of them until it ends (PR #43
// review). A fiber that has exited must still never register again.

/** A host that records each registration and is always inside a slice. */
const countingHost = (registered: number[]): Host => ({
  emit: () => {},
  clock: () => 0,
  draw: () => 0,
  register: (fiber) => {
    registered.push(fiber);
    return false;
  },
  inSlice: () => true,
  foreign: () => {},
  noteGlobal: () => {},
});

/** Admits a suspended fiber, then interrupts it so that it exits. */
const admitThenExit = () => {
  const registered: number[] = [];
  const state = makeState();
  const register = registration(state, countingHost(registered));
  const fiber = Effect.runFork(Effect.never);
  register(fiber);
  const live = state.fibers.size;
  fiber.interruptUnsafe();
  return { registered, state, register, fiber, live };
};

test("a fiber leaves the live map when it exits", () => {
  const { state, fiber, live } = admitThenExit();
  expect(live).toBe(1);
  expect(fiber.pollUnsafe()).toBeDefined();
  expect(state.fibers.size).toBe(0);
});

test("a fiber that has exited does not register again", () => {
  const { registered, register, fiber } = admitThenExit();
  expect(register(fiber)).toBe(false);
  expect(registered).toEqual([0]);
});

