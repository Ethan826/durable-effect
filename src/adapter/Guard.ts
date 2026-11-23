import type { FiberId, Host } from "./Interface.ts";
import type { AnyFiber } from "./State.ts";

type Interrupt = AnyFiber["interruptUnsafe"];

/**
 * The interrupt a registered fiber exposes to other code. Inside a slice it
 * is forwarded to the fiber's original `interruptUnsafe`; outside one it is
 * reported to the host as foreign and dropped, because a timer or callback
 * outside any slice must not change the fiber's trace.
 */
export const guardInterrupt = (
  fiber: FiberId,
  original: Interrupt,
  host: Host,
): Interrupt => (fiberId, annotations) => {
  if (host.inSlice()) original(fiberId, annotations);
  else host.foreign("interrupt", fiber);
};
