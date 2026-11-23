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
    shouldYield: (fiber) => {
      state.register(fiber);
      return fiber.currentOpCount >= maxOpsBeforeYield;
    },
    makeDispatcher: () => dispatcher,
  };
};
