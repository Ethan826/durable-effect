import { guardInterrupt } from "./Guard.ts";
import type { FiberId, Host } from "./Interface.ts";
import { freshFiberId } from "./State.ts";
import type { AdapterState, AnyFiber, RegisteredFiber } from "./State.ts";

/**
 * Reports the fiber's exit, after its finalizers have run, and drops it from
 * the live fibers.
 */
const observeExit = (
  state: AdapterState,
  host: Host,
  fiber: AnyFiber,
  known: RegisteredFiber,
) =>
  fiber.addObserver(() => {
    state.fibers.delete(fiber);
    host.emit({ _tag: "FiberExited", fiber: known.id });
  });

/** Gives a fiber its id, its guarded interrupt and its exit report. */
const admit = (
  state: AdapterState,
  host: Host,
  fiber: AnyFiber,
): RegisteredFiber => {
  const known: RegisteredFiber = {
    id: freshFiberId(state),
    interruptUnsafe: fiber.interruptUnsafe.bind(fiber),
  };
  state.fibers.set(fiber, known);
  state.admitted.add(fiber);
  // The Fiber type marks the field readonly; the adapter owns these fibers.
  Object.defineProperty(fiber, "interruptUnsafe", {
    value: guardInterrupt(known.id, known.interruptUnsafe, host),
  });
  observeExit(state, host, fiber, known);
  return known;
};

/**
 * The registration step the scheduler calls before each operation. A fiber
 * is registered the first time it is seen, which is before its first step.
 * Answers `true` when the host asked for the new fiber to be interrupted;
 * the interrupt goes through the original, and the scheduler then yields so
 * that it fires before the fiber's first operation. A fiber that starts
 * masked is the exception: Effect defers the interrupt until the mask ends,
 * so such a fiber runs its masked steps first.
 */
export const registration =
  (state: AdapterState, host: Host) => (fiber: AnyFiber): boolean => {
    if (state.admitted.has(fiber)) return false;
    const known = admit(state, host, fiber);
    const interrupt = host.register(known.id);
    // On a running fiber the original only sets `_deferredInterrupt`
    // (effect 4.1.5 internal/effect.ts:594-616). The `true` we return makes
    // the loop queue a resume (`yieldNow`, :775-785, so the host sees a
    // `Queue`), then, finding the interrupt deferred, cancel that resume and
    // fail with the interrupt in the same run (:713-723, :689-692). The
    // queued task does nothing, and the fiber never takes its first step,
    // unless it started masked: then the interrupt waits for the mask's end.
    if (interrupt) known.interruptUnsafe();
    return interrupt;
  };

/**
 * `RequestInterrupt`: interrupts the fiber with this id through its original
 * `interruptUnsafe`, since the executor's request is never foreign. An
 * unknown id does nothing; so does a fiber that has exited, which is no
 * longer among the live fibers.
 */
export const requestInterrupt = (state: AdapterState, fiber: FiberId) => {
  const known = [...state.fibers.values()].find(
    (registered) => registered.id === fiber,
  );
  known?.interruptUnsafe();
};
