import { Brand } from "effect";
import type {
  AdapterRuntime,
  Event,
  Task,
  TaskId,
} from "../src/adapter/Interface.ts";
import { makeAdapter } from "../src/adapter/Runtime.ts";
import type { AnyFiber } from "../src/adapter/State.ts";
import { beginRun, fibersRun, openTask, startedKinds } from "./census.ts";
import type { Journal } from "./deliveries.ts";
import type { Program } from "./grammar.ts";
import { scriptedHost } from "./host.ts";
import type { LogEntry, ScriptedHost } from "./host.ts";
import { interpret } from "./interpret.ts";
import type { Variant } from "./mutants.ts";

/**
 * Why a task was sent: by the host's own run (`host`); a task id no one
 * queued, to see that nothing runs (`idle`, I5); a delivery for a token
 * whose release was reported (`late`, I4); or an interruption of a fiber
 * awaiting an even token (`interrupt`, I4).
 */
export type Kind = "host" | "idle" | "late" | "interrupt";

/** One task of a lifecycle run: the log entries it added and its loops. */
export interface TaskRecord {
  readonly task: Task;
  readonly kind: Kind;
  readonly loops: number;
  /** The task's entries are `log.slice(from, to)`, after its `Sent`. */
  readonly from: number;
  readonly to: number;
}

/** What a lifecycle run leaves for the checks. */
export interface LifecycleRun {
  readonly log: ReadonlyArray<LogEntry>;
  readonly records: ReadonlyArray<TaskRecord>;
  /** Every fiber that ran in a task, as the census saw it. */
  readonly fibers: ReadonlyArray<AnyFiber>;
  /** Of those, how many started internal, and how many detached. */
  readonly kinds: { readonly internal: number; readonly detached: number };
}

// Above every id a run queues, so `RunQueued` of it names no task.
const idleTask = Brand.nominal<TaskId>()(Number.MAX_SAFE_INTEGER);

/** The adapter with each task's loops and log entries recorded. */
const recording = (
  host: ScriptedHost,
  inner: AdapterRuntime,
  records: TaskRecord[],
  mark: { kind: Kind },
): AdapterRuntime => ({
  runTask: (task) => {
    const from = host.log.length;
    const loops = openTask(() => inner.runTask(task));
    records.push({ task, kind: mark.kind, loops, from, to: host.log.length });
    mark.kind = "host";
  },
});

const eventsIn = (entries: ReadonlyArray<LogEntry>): ReadonlyArray<Event> =>
  entries.flatMap((entry) => entry._tag === "Emitted" ? [entry.event] : []);

/** Tokens whose await has ended: delivered, cancelled, refused, released. */
const endedTokens = (log: ReadonlyArray<LogEntry>) => new Set([
  ...log.flatMap((entry) =>
    entry._tag === "Sent" && "token" in entry.task ? [entry.task.token] : []
  ),
  ...eventsIn(log).flatMap((event) =>
    event._tag === "Release" ? [event.token] : []
  ),
]);

/** Sends tasks of its own between the host's steps, each then an idle. */
const injector = (host: ScriptedHost, adapter: AdapterRuntime, mark: {
  kind: Kind;
}) => {
  const send = (kind: Kind, task: Task) => {
    mark.kind = kind;
    host.extend(adapter, task);
  };
  const idle = () => send("idle", { _tag: "RunQueued", task: idleTask });
  const inject = (kind: Kind, task: Task) => {
    send(kind, task);
    idle();
  };
  return { idle, inject };
};

type Injector = ReturnType<typeof injector>;

/**
 * After each step: an idle task; a late delivery, `Value` 1, for each
 * release since the last step; and an interruption of each fiber that
 * started an await on an even token since then and still awaits it.
 */
const afterStep = (
  host: ScriptedHost,
  { idle, inject }: Injector,
  cursor: { at: number },
) => {
  const fresh = eventsIn(host.log.slice(cursor.at));
  cursor.at = host.log.length;
  idle();
  fresh.forEach((event) => {
    if (event._tag !== "Release") return;
    const { fiber, token } = event;
    const outcome = { _tag: "Value", value: 1 } as const;
    inject("late", { _tag: "Deliver", fiber, token, outcome });
  });
  const ended = endedTokens(host.log);
  fresh.forEach((event) => {
    if (event._tag !== "Start" || event.token % 2 !== 0) return;
    if (ended.has(event.token)) return;
    inject("interrupt", { _tag: "RequestInterrupt", fiber: event.fiber });
  });
};

/** The adapter, recorded, with the injector that sends tasks into it. */
const instrumented = (host: ScriptedHost, inner: AdapterRuntime) => {
  const records: TaskRecord[] = [];
  const mark: { kind: Kind } = { kind: "host" };
  const adapter = recording(host, inner, records, mark);
  return { adapter, records, inject: injector(host, adapter, mark) };
};

/**
 * Runs a program under the adapter, or a variant, with the scripted host
 * paced so that the lifecycle tasks go in between its steps.
 */
export const lifecycleRun = async (
  [program, journal]: readonly [Program, Journal],
  seed: number,
  make: Variant = makeAdapter,
): Promise<LifecycleRun> => {
  beginRun();
  const host = scriptedHost(journal, { seed });
  const run = instrumented(host, make(interpret(program), 0, host));
  const cursor = { at: 0 };
  await host.runPaced(run.adapter, async () => {
    afterStep(host, run.inject, cursor);
  });
  afterStep(host, run.inject, cursor);
  const fibers = fibersRun();
  return { log: host.log, records: run.records, fibers, kinds: startedKinds() };
};
