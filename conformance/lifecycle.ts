import { Brand, Fiber } from "effect";
import type { Effect } from "effect";
import type { Durable } from "../src/adapter/Durable.ts";
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
  /** Every registration, with the host's answer and Effect's mask. */
  readonly registrations: ReadonlyArray<Registration>;
}

// Above every id a run queues, so `RunQueued` of it names no task.
const idleTask = Brand.nominal<TaskId>()(Number.MAX_SAFE_INTEGER);

/**
 * One `register` question: the fiber, whether the host asked for its
 * interruption (it does while closing), and whether Effect had the fiber
 * masked as it registered, by its own `interruptible` flag.
 */
export interface Registration {
  readonly fiber: number;
  readonly closing: boolean;
  readonly masked: boolean;
}

/** The Effect fibers by registered id, and every registration. */
interface Registry {
  readonly fibers: Map<number, AnyFiber>;
  readonly registrations: Registration[];
}

const isMasked = (fiber: AnyFiber) =>
  Reflect.get(fiber, "interruptible") === false;

/**
 * The host the adapter talks to: each `register` question notes the
 * fiber asking, which is the current one: the adapter registers a fiber
 * from inside its own run loop (Fibers.ts, Scheduler.ts).
 */
const noting = (host: Host, registry: Registry): Host => ({
  ...host,
  register: (fiber) => {
    const current = Fiber.getCurrent();
    const closing = host.register(fiber);
    if (current === undefined) return closing;
    registry.fibers.set(fiber, current);
    const masked = isMasked(current);
    registry.registrations.push({ fiber, closing, masked });
    return closing;
  },
});

/** Effect's own mask on the fiber a request names, if it is known. */
const maskOf = (registry: Registry, task: Task) => {
  const fiber = "fiber" in task ? registry.fibers.get(task.fiber) : undefined;
  return fiber === undefined ? undefined : isMasked(fiber);
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

/** A handler as the adapter takes it. */
export type Handler = Effect.Effect<unknown, unknown, Durable>;

/** The adapter, recorded, with the injector that sends tasks into it. */
const instrumented = (host: ScriptedHost, handler: Handler, make: Variant) => {
  const records: TaskRecord[] = [];
  const mark: Mark = { kind: "host" };
  const registry: Registry = { fibers: new Map(), registrations: [] };
  const adapter = recording(host, make(handler, 0, noting(host, registry)),
    records, mark, registry);
  return { adapter, records, inject: injector(host, adapter, mark), registry };
};

/**
 * Runs a handler written directly in Effect, as `lifecycleRun` runs a
 * program of the grammar; `program` is what the shape counts read, and
 * is empty for such a handler.
 */
export const lifecycleRunOf = async (
  handler: Handler,
  sampled: readonly [Program, Journal],
  seed: number,
  make: Variant = makeAdapter,
): Promise<LifecycleRun> => {
  beginRun();
  const host = scriptedHost(sampled[1], { seed });
  const run = instrumented(host, handler, make);
  const cursor = { at: 0 };
  await host.runPaced(run.adapter, async () => {
    afterStep(host, run.inject, cursor);
  });
  afterStep(host, run.inject, cursor);
  return {
    program: sampled[0], log: host.log, records: run.records,
    fibers: fibersRun(),
    kinds: startedKinds(), registrations: run.registry.registrations,
  };
};

/**
 * Runs a program under the adapter, or a variant, with the scripted host
 * paced so that the lifecycle tasks go in between its steps.
 */
export const lifecycleRun = (
  sampled: readonly [Program, Journal],
  seed: number,
  make: Variant = makeAdapter,
): Promise<LifecycleRun> =>
  lifecycleRunOf(interpret(sampled[0]), sampled, seed, make);
