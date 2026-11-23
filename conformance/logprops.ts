import type { Event, Task } from "../src/adapter/Interface.ts";
import type { LogEntry } from "./host.ts";

// The log properties of verification/proofs/Executor/Runtime.v, written
// again over the scripted host's log. Nothing here reads the adapter: each
// check walks the log as the Coq definition named beside it does.

/** A log entry as Runtime.v's `LogEntry` has it; the rest are dropped. */
export type CoqEntry =
  | { readonly _tag: "LTask"; readonly task: Task }
  | { readonly _tag: "LEvent"; readonly event: Event }
  | {
    readonly _tag: "LClock" | "LDraw" | "LRegister";
    readonly fiber: number;
  };

const questionTags = {
  clock: "LClock",
  draw: "LDraw",
  register: "LRegister",
} as const;

/**
 * `Sent` is `LTask`, `Emitted` is `LEvent`, and each answer is `LClock`,
 * `LDraw` or `LRegister`. `Foreign`, `Global`, `Blocked` and `Discarded`
 * are the host's own notes, outside Runtime.v's log.
 */
const toCoq = (entry: LogEntry): ReadonlyArray<CoqEntry> => {
  if (entry._tag === "Sent") return [{ _tag: "LTask", task: entry.task }];
  if (entry._tag === "Emitted") return [{ _tag: "LEvent", event: entry.event }];
  if (entry._tag !== "Answered") return [];
  return [{ _tag: questionTags[entry.question], fiber: entry.fiber }];
};

/** The log as Runtime.v's `LogEntry` list. */
export const coqLog = (log: ReadonlyArray<LogEntry>) => log.flatMap(toCoq);

/** Runtime.v `entry_fiber`: the fiber an event or answer is about. */
export const entryFiber = (entry: CoqEntry): number | undefined => {
  if (entry._tag !== "LEvent") {
    return entry._tag === "LTask" ? undefined : entry.fiber;
  }
  const event = entry.event;
  const attributed = event._tag === "Start" || event._tag === "Release" ||
    event._tag === "FiberExited";
  return attributed ? event.fiber : undefined;
};

const isDelivery = (task: Task) => task._tag === "Deliver" ||
  task._tag === "DeliverCancel" || task._tag === "DeliverDefect";

/** Runtime.v `ends_await`: a delivery for the await, or its release. */
const endsAwait = (fiber: number, token: number) => (entry: CoqEntry) => {
  if (entry._tag === "LTask") {
    const { task } = entry;
    return isDelivery(task) && "token" in task && task.fiber === fiber &&
      task.token === token;
  }
  return entry._tag === "LEvent" && entry.event._tag === "Release" &&
    entry.event.fiber === fiber && entry.event.token === token;
};

/**
 * Runtime.v `quiet_until_end`: the index of the first entry about `fiber`
 * before the await of `token` ends, if there is one.
 */
const loudBeforeEnd = (
  fiber: number,
  token: number,
  rest: ReadonlyArray<CoqEntry>,
): number | undefined => {
  const end = rest.findIndex(endsAwait(fiber, token));
  const quiet = end === -1 ? rest : rest.slice(0, end);
  const loud = quiet.findIndex((entry) => entryFiber(entry) === fiber);
  return loud === -1 ? undefined : loud;
};

const startOf = (entry: CoqEntry) =>
  entry._tag === "LEvent" && entry.event._tag === "Start"
    ? entry.event
    : undefined;

/** A repeated value in a list, if there is one. */
const repeatIn = (values: ReadonlyArray<number>): number | undefined =>
  values.find((value, at) => values.indexOf(value) !== at);

/**
 * Runtime.v `I4` on one log: after each `EvStart f tok`, nothing about `f`
 * until the await ends (`quiet_until_end`), and `start_tokens` has no
 * repeat (`NoDup`). Answers the first breach, described.
 */
export const i4Breach = (log: ReadonlyArray<CoqEntry>): string | undefined => {
  const tokens = log.flatMap((entry) => startOf(entry)?.token ?? []);
  const twice = repeatIn(tokens);
  if (twice !== undefined) return `token ${twice} started twice`;
  const breaches = log.flatMap((entry, at) => {
    const start = startOf(entry);
    if (start === undefined) return [];
    const loud = loudBeforeEnd(start.fiber, start.token, log.slice(at + 1));
    return loud === undefined ? [] : [`fiber ${start.fiber} acts at entry ` +
      `${at + 1 + loud} before its await of token ${start.token} ends`];
  });
  return breaches[0];
};

const isRootExit = (entry: CoqEntry) =>
  entry._tag === "LEvent" && entry.event._tag === "RootExit";

/** Runtime.v `first_registered`. */
const firstRegistered = (log: ReadonlyArray<CoqEntry>) =>
  log.find((entry) => entry._tag === "LRegister");

const exitedIn = (log: ReadonlyArray<CoqEntry>, fiber: number) =>
  log.some((entry) => entry._tag === "LEvent" &&
    entry.event._tag === "FiberExited" && entry.event.fiber === fiber);

/** I6's second half for the root exit at `at`, described if broken. */
const exitTooEarly = (log: ReadonlyArray<CoqEntry>, at: number) => {
  const pre = log.slice(0, at);
  const root = firstRegistered(pre);
  if (root === undefined || !("fiber" in root)) {
    return `root exit at entry ${at} before any fiber registered`;
  }
  return exitedIn(pre, root.fiber) ? undefined
    : `root exit at entry ${at} before fiber ${root.fiber} exited`;
};

/**
 * Runtime.v `I6` on one log: `root_exits` at most 1, and each root exit
 * after the `EvFiberExited` of the first fiber registered.
 */
export const i6Breach = (log: ReadonlyArray<CoqEntry>): string | undefined => {
  const exits = log.flatMap((entry, at) => isRootExit(entry) ? [at] : []);
  if (exits.length > 1) return `${exits.length} root exits`;
  return exits.flatMap((at) => exitTooEarly(log, at) ?? [])[0];
};

/** Runtime.v `I7` on one log: `started` (the registrations) has no repeat. */
export const i7Breach = (log: ReadonlyArray<CoqEntry>): string | undefined => {
  const started = log.flatMap((entry) =>
    entry._tag === "LRegister" ? [entry.fiber] : []
  );
  const twice = repeatIn(started);
  return twice === undefined ? undefined : `fiber ${twice} registered twice`;
};

const exitOf = (entry: CoqEntry) =>
  entry._tag === "LEvent" && entry.event._tag === "FiberExited"
    ? entry.event.fiber
    : undefined;

/** I8 for one entry, given the fibers registered and exited before it. */
const outOfLife = (
  entry: CoqEntry,
  registered: ReadonlySet<number>,
  exited: ReadonlySet<number>,
): string | undefined => {
  const fiber = entryFiber(entry);
  if (fiber === undefined) return undefined;
  const isRegister = entry._tag === "LRegister";
  if (!isRegister && !registered.has(fiber)) return `fiber ${fiber} unborn`;
  return exited.has(fiber) ? `fiber ${fiber} after its exit` : undefined;
};

/**
 * Runtime.v `I8` on one log: each entry about a fiber is its `LRegister`
 * or follows one, and none follows its `EvFiberExited`.
 */
export const i8Breach = (log: ReadonlyArray<CoqEntry>): string | undefined => {
  const registered = new Set<number>();
  const exited = new Set<number>();
  const breaches = log.flatMap((entry, at) => {
    const breach = outOfLife(entry, registered, exited);
    if (entry._tag === "LRegister") registered.add(entry.fiber);
    const gone = exitOf(entry);
    if (gone !== undefined) exited.add(gone);
    return breach === undefined ? [] : [`entry ${at}: ${breach}`];
  });
  return breaches[0];
};
