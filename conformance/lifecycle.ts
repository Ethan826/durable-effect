import { Brand, Fiber } from "effect";
import type {
  AdapterRuntime,
  Event,
  Host,
  Task,
  TaskId,
} from "../src/adapter/Interface.ts";
import { makeAdapter } from "../src/adapter/Runtime.ts";
import type { AnyFiber } from "../src/adapter/State.ts";
import { beginRun, fibersRun, openTask, startedKinds } from "./census.ts";
import type { Started } from "./census.ts";
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
  /**
   * For a `RequestInterrupt`: whether Effect had the target fiber masked
   * when the request was sent (its own `interruptible` flag, :594-616), read
   * before the task, not from anything the adapter reported.
   */
  readonly masked?: boolean | undefined;
}

/** Why the next task is sent. */
interface Mark {
  kind: Kind;
}

/** What a lifecycle run leaves for the checks. */
export interface LifecycleRun {
  readonly program: Program;
  readonly log: ReadonlyArray<LogEntry>;
  readonly records: ReadonlyArray<TaskRecord>;
  /** Every fiber that ran in a task, as the census saw it. */
  readonly fibers: ReadonlyArray<AnyFiber>;
  /** Of those, how many started internal or detached; inline wakes. */
  readonly kinds: Started;
}

// Above every id a run queues, so `RunQueued` of it names no task.
const idleTask = Brand.nominal<TaskId>()(Number.MAX_SAFE_INTEGER);

/** The Effect fibers by the ids the adapter registered them under. */
type Registry = Map<number, AnyFiber>;

/**
 * The host the adapter talks to: each `register` question notes the
 * fiber asking, which is the current one: the adapter registers a fiber
 * from inside its own run loop (Fibers.ts, Scheduler.ts).
 */
const noting = (host: Host, registry: Registry): Host => ({
  ...host,
  register: (fiber) => {
    const current = Fiber.getCurrent();
    if (current !== undefined) registry.set(fiber, current);
    return host.register(fiber);
  },
});

/** Effect's own mask on the fiber a request names, if it is known. */
const maskOf = (registry: Registry, task: Task) => {
  const fiber = "fiber" in task ? registry.get(task.fiber) : undefined;
  return fiber === undefined ? undefined
    : Reflect.get(fiber, "interruptible") === false;
};

/** The adapter with each task's loops and log entries recorded. */
const recording = (
  host: ScriptedHost,
  inner: AdapterRuntime,
  records: TaskRecord[],
  mark: Mark,
  registry: Registry,
): AdapterRuntime => ({
  runTask: (task) => {
    const from = host.log.length;
    const masked = task._tag === "RequestInterrupt"
      ? maskOf(registry, task)
      : undefined;
    const loops = openTask(() => inner.runTask(task));
    const { kind } = mark;
    records.push({ task, kind, loops, from, to: host.log.length, masked });
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
const injector = (
  host: ScriptedHost,
  adapter: AdapterRuntime,
  mark: Mark,
) => {
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
const instrumented = (host: ScriptedHost, program: Program, make: Variant) => {
  const records: TaskRecord[] = [];
  const mark: Mark = { kind: "host" };
  const registry: Registry = new Map();
  const inner = make(interpret(program), 0, noting(host, registry));
  const adapter = recording(host, inner, records, mark, registry);
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
  const run = instrumented(host, program, make);
  const cursor = { at: 0 };
  await host.runPaced(run.adapter, async () => {
    afterStep(host, run.inject, cursor);
  });
  afterStep(host, run.inject, cursor);
  return {
    program, log: host.log, records: run.records,
    fibers: fibersRun(), kinds: startedKinds(),
  };
};
