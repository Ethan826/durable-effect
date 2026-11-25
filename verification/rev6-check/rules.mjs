// rules.mjs: the executor of design revision 6, part 1 (comment
// 7142428658), as the system under test of the step 7 check. It also holds
// a small stand-in for Effect's runtime (fibers, masks, finalizers,
// structured concurrency), taken as given by the interface I1 to I9 of #37.
// A turn is atomic (X4's slices are excluded by step 7).
//
// Interface with the environment (env.mjs). Nothing else crosses it.
//   The executor calls only these methods of `io`:
//     issue(cmd) -> idx, enterClosure(idx), refuseClosure(idx),
//     abortSignal(idx), returnResult(idx, value), returnRetryable(idx),
//     writeOutput(outcome), failRetryable(), emit(event), now()
//   The environment, through model.mjs, calls:
//     createExecutor(program, config)  config: {invocationId, inactivity,
//                                      mutant}
//     startAttempt(exec, io)           the first turn issues its sample
//     raceMembers(exec)                null when not awaiting; else keys
//                                      "r:<idx>" and "i:<idx>"
//     onConsume(exec, io, entry)       the race resolved with entry
//     onWrapperCalled(exec, io, idx)   the SDK called the run's wrapper
//     onClosureSettled(exec, io, idx, raw)
//     onEnded(exec, io)                Restate's abort timeout (C7)
//     onTick(exec, io)                 the executor's timer (warnings)
//     progress(exec, io) -> boolean    one deterministic step, if any
//     checkWarnings(exec, io)          the first warning (C16)
//
// The executor's code is in the modules of rules/; this file re-exports
// the interface above from them.

export { createExecutor, raceMembers, startAttempt } from "./rules/base.mjs";
export { onConsume, onWrapperCalled } from "./rules/consume.mjs";
export { onClosureSettled, onEnded, progress } from "./rules/closing.mjs";
export { checkWarnings, onTick } from "./rules/warnings.mjs";
