import type { Scheduler } from "effect";
import type { Host } from "./Interface.ts";
import { freshTaskId } from "./State.ts";
import type { AdapterState, AnyFiber } from "./State.ts";

/** Effect's default operation budget (`MaxOpsBeforeYield`). */
const maxOpsBeforeYield = 2048;

/**
 * The resume guard (#37 I3; owner's approval on #27). A fiber that runs
 * outside a slice was resumed by code the executor did not run: report it
 * as foreign and answer `true`, so the fiber yields before its next step
 * and the resumed continuation never runs. The yield queues a task outside
 * the slice, which the executor discards; the adapter does not know that.
 */
const foreignResume = (
  state: AdapterState,
  host: Host,
  fiber: AnyFiber,
): boolean => {
  if (host.inSlice()) return false;
  const known = state.fibers.get(fiber);
  if (known !== undefined) host.foreign("resume", known.id);
  return true;
};

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
    // Register first, so a fiber registers at its first operation; then
    // the slice check; then the budget. Yield when registration has just
    // asked for an interruption, so it fires before the fiber's first
    // operation; when the fiber runs outside a slice; or when the budget
    // is spent. A fiber that starts masked is not interrupted before its
    // first step: Effect defers the interrupt until the mask ends.
    shouldYield: (fiber) => {
      const interrupting = state.register(fiber);
      const foreign = foreignResume(state, host, fiber);
      return interrupting || foreign ||
        fiber.currentOpCount >= maxOpsBeforeYield;
    },
    makeDispatcher: () => dispatcher,
  };
};
