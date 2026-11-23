import type { FiberId, Task } from "../src/adapter/Interface.ts";
import type { LogEntry } from "./host.ts";
import { eventsIn, registered, starts } from "./sequences.ts";

// What the arbitrary task sequences looked at: the tasks the executor
// never sends that a run sent, and the awaits and root exits it holds.

/**
 * What a run's checks looked at: the tasks the executor never sends, and
 * the awaits and root exits I4 and I6 judge.
 */
export interface Unusual {
  readonly secondStarts: number;
  readonly strayDeliveries: number;
  readonly staleInterrupts: number;
  readonly awaits: number;
  readonly rootExits: number;
}

/** Whether a `StartRoot` follows another. */
const secondStart = (before: ReadonlyArray<LogEntry>) =>
  before.some((entry) =>
    entry._tag === "Sent" && entry.task._tag === "StartRoot"
  );

/** Whether a fiber is not live: never registered, or exited. */
const notLive = (fiber: FiberId, before: ReadonlyArray<LogEntry>) =>
  !registered(before).includes(fiber) || eventsIn(before).some((event) =>
    event._tag === "FiberExited" && event.fiber === fiber
  );

/** Whether no fiber awaits this token now: never started, or ended. */
const notAwaited = (
  fiber: number,
  tok: number,
  before: ReadonlyArray<LogEntry>,
) => {
  const started = starts(before).some((start) =>
    start.token === tok && start.fiber === fiber
  );
  const answered = before.some((entry) => entry._tag === "Sent" &&
    "token" in entry.task && entry.task.token === tok);
  const released = eventsIn(before).some((event) =>
    event._tag === "Release" && event.token === tok
  );
  return !started || answered || released;
};

/** Which kind of task the executor never sends this is, if any. */
const strayKind = (task: Task, before: ReadonlyArray<LogEntry>) => {
  if (task._tag === "StartRoot") {
    return secondStart(before) ? "secondStarts" : undefined;
  }
  if (task._tag === "RequestInterrupt") {
    return notLive(task.fiber, before) ? "staleInterrupts" : undefined;
  }
  if (!("token" in task)) return undefined;
  return notAwaited(task.fiber, task.token, before) ? "strayDeliveries"
    : undefined;
};

/** Counts a log's unusual tasks, its awaits and its root exits. */
export const unusualIn = (log: ReadonlyArray<LogEntry>): Unusual => {
  const counts = {
    secondStarts: 0, strayDeliveries: 0, staleInterrupts: 0,
    awaits: starts(log).length,
    rootExits: eventsIn(log).filter((event) => event._tag === "RootExit")
      .length,
  };
  log.forEach((entry, at) => {
    if (entry._tag !== "Sent") return;
    const kind = strayKind(entry.task, log.slice(0, at));
    if (kind !== undefined) counts[kind] += 1;
  });
  return counts;
};
