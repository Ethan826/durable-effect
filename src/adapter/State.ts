import { Brand } from "effect";
import type { Fiber } from "effect";
import type { FiberId, TaskId, Token } from "./Interface.ts";

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
  /**
   * Called by the scheduler for each fiber it checks. Answers `true` when it
   * has just asked for that fiber to be interrupted (see `Fibers.ts`).
   */
  register: (fiber: AnyFiber) => boolean;
}

/** A fresh state: counters at zero, no tasks, no fibers. */
export const makeState = (): AdapterState => ({
  nextFiber: 0,
  nextToken: 0,
  nextTask: 0,
  tasks: new Map(),
  fibers: new Map(),
  register: () => false,
});

// A counter starts at zero and only counts up, so each value it gives is a
// natural number and needs no check. Unchecked brands also cannot throw.
const fiberId = Brand.nominal<FiberId>();
const token = Brand.nominal<Token>();
const taskId = Brand.nominal<TaskId>();

/** Takes the next fiber id from this state's counter. */
export const freshFiberId = (state: AdapterState): FiberId =>
  fiberId(state.nextFiber++);

/** Takes the next await token from this state's counter. */
export const freshToken = (state: AdapterState): Token =>
  token(state.nextToken++);

/** Takes the next task id from this state's counter. */
export const freshTaskId = (state: AdapterState): TaskId =>
  taskId(state.nextTask++);
