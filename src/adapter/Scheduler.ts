import type { Scheduler } from "effect";
import type { Host } from "./Interface.ts";
import { freshTaskId } from "./State.ts";
import type { AdapterState } from "./State.ts";

/** Effect's default operation budget (`MaxOpsBeforeYield`). */
const maxOpsBeforeYield = 2048;

/**
 * A scheduler that runs nothing itself. A scheduled thunk is stored under a
 * fresh task id and reported as `Queue`; the executor decides when it runs.
 */
export const deterministicScheduler = (
  state: AdapterState,
  host: Host,
): Scheduler.Scheduler => {
  const dispatcher: Scheduler.SchedulerDispatcher = {
    scheduleTask: (thunk, priority) => {
      const task = freshTaskId(state);
      state.tasks.set(task, thunk);
      host.emit({ _tag: "Queue", priority, task });
    },
    // Queued work runs only when the executor sends `RunQueued`.
    flush: () => {},
  };
  return {
    executionMode: "sync",
    // Yield when registration has just asked for an interruption, so it
    // fires before the fiber's first operation, or when the budget is spent.
    // A fiber that starts masked is not interrupted before its first step:
    // Effect defers the interrupt until the mask ends.
    shouldYield: (fiber) => {
      const interrupting = state.register(fiber);
      return interrupting || fiber.currentOpCount >= maxOpsBeforeYield;
    },
    makeDispatcher: () => dispatcher,
  };
};
