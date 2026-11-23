import { Schema } from "effect";
import type { Fiber } from "effect";
import { FiberId, TaskId, Token } from "./Interface.ts";

/** Any fiber the adapter runs. */
export type AnyFiber = Fiber.Fiber<unknown, unknown>;

/** A fiber the adapter knows, with the `interruptUnsafe` it started with. */
export interface RegisteredFiber {
  readonly id: FiberId;
  readonly interruptUnsafe: AnyFiber["interruptUnsafe"];
}

/**
 * Everything one adapter remembers. Counters live here, not in the module,
 * so two adapters in one process never share numbers.
 */
export interface AdapterState {
  nextFiber: number;
  nextToken: number;
  nextTask: number;
  /** Queued thunks, by the task id the executor was told. */
  readonly tasks: Map<TaskId, () => void>;
  /** Fibers seen so far, with their original `interruptUnsafe`. */
  readonly fibers: Map<AnyFiber, RegisteredFiber>;
  /** Called by the scheduler for each fiber it checks; Task 6 fills it in. */
  register: (fiber: AnyFiber) => void;
}

/** A fresh state: counters at zero, no tasks, no fibers. */
export const makeState = (): AdapterState => ({
  nextFiber: 0,
  nextToken: 0,
  nextTask: 0,
  tasks: new Map(),
  fibers: new Map(),
  register: () => {},
});

/** Takes the next fiber id from this state's counter. */
export const freshFiberId = (state: AdapterState): FiberId =>
  Schema.decodeSync(FiberId)(state.nextFiber++);

/** Takes the next await token from this state's counter. */
export const freshToken = (state: AdapterState): Token =>
  Schema.decodeSync(Token)(state.nextToken++);

/** Takes the next task id from this state's counter. */
export const freshTaskId = (state: AdapterState): TaskId =>
  Schema.decodeSync(TaskId)(state.nextTask++);
