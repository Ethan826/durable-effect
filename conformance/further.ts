import { Brand } from "effect";
import type {
  Event,
  FiberId,
  Task,
  TaskId,
  Token,
} from "../src/adapter/Interface.ts";
import type { LogEntry } from "./host.ts";

// Built from ids the log holds, or one past the largest: naturals.
const fiberId = Brand.nominal<FiberId>();
const token = Brand.nominal<Token>();
const taskId = Brand.nominal<TaskId>();

type Tagged<T extends Event["_tag"]> = Extract<Event, { readonly _tag: T }>;

const isTag = <T extends Event["_tag"]>(tag: T) =>
  (event: Event): event is Tagged<T> => event._tag === tag;

/** The events the adapter emitted with this tag, in order. */
const emitted = <T extends Event["_tag"]>(
  log: ReadonlyArray<LogEntry>,
  tag: T,
): ReadonlyArray<Tagged<T>> =>
  log.flatMap((entry) => entry._tag === "Emitted" ? [entry.event] : [])
    .filter(isTag(tag));

const nextAfter = (ids: ReadonlyArray<number>) =>
  ids.reduce((top, id) => Math.max(top, id + 1), 0);

/** A queued task: the task id after every id the adapter has queued. */
const queuedProbe = (log: ReadonlyArray<LogEntry>): Task => ({
  _tag: "RunQueued",
  task: taskId(nextAfter(emitted(log, "Queue").map((queued) => queued.task))),
});

/** Tokens a delivery or a release has settled. */
const settled = (log: ReadonlyArray<LogEntry>) => new Set([
  ...log.flatMap((entry) =>
    entry._tag === "Sent" && "token" in entry.task ? [entry.task.token] : []
  ),
  ...emitted(log, "Release").map((release) => release.token),
]);

/**
 * A delivery: `Value` 1 to the oldest token still awaited, or else to the
 * token after every one the adapter has started, for fiber 0.
 */
const deliveryProbe = (log: ReadonlyArray<LogEntry>): Task => {
  const starts = emitted(log, "Start");
  const done = settled(log);
  const open = starts.find((start) => !done.has(start.token));
  const fresh = token(nextAfter(starts.map((start) => start.token)));
  return {
    _tag: "Deliver",
    fiber: open?.fiber ?? fiberId(0),
    token: open?.token ?? fresh,
    outcome: { _tag: "Value", value: 1 },
  };
};

/** An interruption request: the lowest live fiber, else fiber 0. */
const interruptProbe = (log: ReadonlyArray<LogEntry>): Task => {
  const exited = new Set(
    emitted(log, "FiberExited").map((exit) => exit.fiber),
  );
  const live = log.flatMap((entry) =>
    entry._tag === "Answered" && entry.question === "register" &&
      !exited.has(entry.fiber)
      ? [entry.fiber]
      : []
  );
  const lowest = live.reduce((low, fiber) => Math.min(low, fiber), Infinity);
  return {
    _tag: "RequestInterrupt",
    fiber: fiberId(Number.isFinite(lowest) ? lowest : 0),
  };
};

/**
 * The three further tasks run from a run's final state (dossier, I1): a
 * queued task, a delivery and an interruption request, chosen from the log
 * alone, so equal logs give equal tasks.
 */
export const further = (log: ReadonlyArray<LogEntry>): ReadonlyArray<Task> => [
  queuedProbe(log),
  deliveryProbe(log),
  interruptProbe(log),
];
