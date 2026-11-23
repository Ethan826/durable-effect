import { Effect, HashSet, Scheduler } from "effect";
import type { Durable } from "../src/adapter/Durable.ts";
import type {
  AdapterRuntime,
  Event,
  Host,
  Task,
  TaskId,
  Token,
} from "../src/adapter/Interface.ts";
import { makeAdapter } from "../src/adapter/Runtime.ts";
import { withGlobalSourceLog } from "../src/adapter/Services.ts";
import { guardMutants } from "./guardmutants.ts";
import { lifeMutants } from "./lifemutants.ts";
import { renumbered } from "./renumber.ts";

/** An interface property of #37 that this suite tests. */
export type Property = "I1" | "I2" | "I7" | "I9";

/** An adapter: `makeAdapter` or a variant of it with the same shape. */
export type Variant = <A, E>(
  program: Effect.Effect<A, E, Durable>,
  seed: number,
  host: Host,
) => AdapterRuntime;

/** A variant of the adapter, and the property it must make fail. */
export interface Mutant {
  readonly property: Property;
  readonly make: Variant;
}

/** True when the second of two queued tasks should run first. */
type Choose = (first: TaskId, second: TaskId) => boolean;

/**
 * Runs the oldest of the queued tasks, or the second oldest when `choose`
 * says so. The host sends one `RunQueued` per `Queue`, so every queued
 * task still runs once; only the order changes.
 */
const pickQueued = (pending: TaskId[], choose: Choose, task: Task): Task => {
  const [first, second] = pending;
  if (first === undefined) return task;
  const takeSecond = second !== undefined && choose(first, second);
  pending.splice(takeSecond ? 1 : 0, 1);
  return { _tag: "RunQueued", task: takeSecond ? second : first };
};

/** The adapter, with the order of two queued tasks decided by `choose`. */
const reordered = (chooser: (host: Host) => Choose): Variant =>
  (program, seed, host) => {
    const pending: TaskId[] = [];
    const noting: Host = {
      ...host,
      emit: (event) => {
        if (event._tag === "Queue") pending.push(event.task);
        host.emit(event);
      },
    };
    const inner = makeAdapter(program, seed, noting);
    const choose = chooser(host);
    const route = (task: Task) =>
      task._tag === "RunQueued" ? pickQueued(pending, choose, task) : task;
    return { runTask: (task) => inner.runTask(route(task)) };
  };

/** I1: `Math.random` chooses between two queued tasks. */
const randomChoice = () => () => Math.random() < 0.5;

/**
 * I2: the iteration order of a HashSet of task handles chooses. A function
 * has no structural hash, so Effect hashes it from `Math.random`.
 */
const hashSetChoice = () => (first: TaskId, second: TaskId) => {
  const handles = HashSet.make(() => first, () => second);
  const [head] = handles;
  return head?.() === second;
};

/**
 * I2: a timer created during a task writes a cell, and a later task reads
 * it to choose. Whether the timer has fired depends on the event loop.
 */
const timerCell = (host: Host): Choose => {
  const cell = { written: false, armed: false };
  const write = () => {
    cell.written = true;
    cell.armed = false;
  };
  return () => {
    const written = cell.written;
    cell.written = false;
    if (!cell.armed) withGlobalSourceLog(host, () => setTimeout(write, 0));
    cell.armed = true;
    return written;
  };
};

type Delivery = Extract<
  Task,
  { readonly _tag: "Deliver" | "DeliverCancel" | "DeliverDefect" }
>;
const isDelivery = (task: Task): task is Delivery =>
  task._tag === "Deliver" || task._tag === "DeliverCancel" ||
  task._tag === "DeliverDefect";

/** The adapter, with each delivery handed to `later` to run. */
const deferred = (later: (host: Host, run: () => void) => void): Variant =>
  (program, seed, host) => {
    const inner = makeAdapter(program, seed, host);
    const runTask = (task: Task) =>
      isDelivery(task)
        ? later(host, () => inner.runTask(task))
        : inner.runTask(task);
    return { runTask };
  };

/** I2: a delivery resumes its fiber from `setTimeout`, called in a task. */
const timeoutResume = deferred((host, run) =>
  withGlobalSourceLog(host, () => {
    setTimeout(run, 0);
  })
);

// Taken when this module loads, before any task, so the adapter's log of
// global sources never sees it used.
const capturedSetTimeout = globalThis.setTimeout;

/** I2: as `timeoutResume`, through a `setTimeout` captured beforehand. */
const capturedTimer = deferred((_, run) => {
  capturedSetTimeout(run, 0);
});

/** The tokens awaited now, kept from the events `host` passes on. */
const awaitedTokens = (host: Host) => {
  const awaited = new Set<Token>();
  const noting: Host = {
    ...host,
    emit: (event) => {
      if (event._tag === "Start") awaited.add(event.token);
      if (event._tag === "Release") awaited.delete(event.token);
      host.emit(event);
    },
  };
  return { awaited, noting };
};

/** A `Release` for a delivery to a token no fiber awaits. */
const staleRelease = (
  awaited: ReadonlySet<Token>,
  task: Task,
): Event | undefined =>
  isDelivery(task) && !awaited.has(task.token)
    ? { _tag: "Release", fiber: task.fiber, token: task.token }
    : undefined;

/**
 * I1: a bit drawn when the adapter is made, read only by a late branch: a
 * delivery for a token no fiber awaits reports a `Release` when it is set.
 * The program's own run never sends such a delivery.
 */
const privateBit: Variant = (program, seed, host) => {
  const bit = Math.random() < 0.5;
  const { awaited, noting } = awaitedTokens(host);
  const inner = makeAdapter(program, seed, noting);
  // Decided before the task runs: a delivered cancel reports its own
  // release, which must not make the token look stale.
  const runTask = (task: Task) => {
    const release = bit ? staleRelease(awaited, task) : undefined;
    if (isDelivery(task)) awaited.delete(task.token);
    inner.runTask(task);
    if (release !== undefined) host.emit(release);
  };
  return { runTask };
};

/** A scheduler that asks `inner`, so fibers register, but never yields. */
const withoutYield = (inner: Scheduler.Scheduler): Scheduler.Scheduler => ({
  executionMode: inner.executionMode,
  makeDispatcher: () => inner.makeDispatcher(),
  shouldYield: (fiber) => {
    inner.shouldYield(fiber);
    return false;
  },
});

/** I9: every fiber of the program runs under a scheduler that never yields. */
const neverYields: Variant = (program, seed, host) =>
  makeAdapter(Effect.withFiber((fiber) =>
    Effect.provideService(program, Scheduler.Scheduler,
      withoutYield(fiber.getRef(Scheduler.Scheduler)))
  ), seed, host);

/** The names of the mutants, for decoding a job. */
export const mutantNames = [
  "randomChoice", "privateBit", "timeoutResume", "timerCell",
  "capturedTimer", "hashSetOrder", "processCounter", "sameIdentity",
  "reuseExited", "neverYields",
] as const;

/** A mutant's name. */
export type MutantName = typeof mutantNames[number];

/** Each mutant #37's table lists for I1, I2, I7 and I9, by name. */
export const mutants: Readonly<Record<MutantName, Mutant>> = {
  randomChoice: { property: "I1", make: reordered(randomChoice) },
  privateBit: { property: "I1", make: privateBit },
  timeoutResume: { property: "I2", make: timeoutResume },
  timerCell: { property: "I2", make: reordered(timerCell) },
  capturedTimer: { property: "I2", make: capturedTimer },
  hashSetOrder: { property: "I2", make: reordered(hashSetChoice) },
  processCounter: { property: "I7", make: renumbered("processCounter") },
  sameIdentity: { property: "I7", make: renumbered("sameIdentity") },
  reuseExited: { property: "I7", make: renumbered("reuseExited") },
  neverYields: { property: "I9", make: neverYields },
};

/** A property of #37 that the lifecycle suite tests. */
export type LifecycleProperty = "I3" | "I4" | "I5" | "I6" | "I8";

/** A variant of the adapter, and the lifecycle property it must fail. */
export interface LifecycleMutant {
  readonly property: LifecycleProperty;
  readonly make: Variant;
}

const lifecycleOf = (property: LifecycleProperty, make: Variant) =>
  ({ property, make });

/**
 * Each mutant #37's table lists for I3, I4, I5, I6 and I8, by name. They
 * live in guardmutants.ts (I3) and lifemutants.ts (the rest), so that this
 * module stays under 250 lines.
 */
export const lifecycleMutants = {
  preventYield: lifecycleOf("I3", guardMutants.preventYield),
  runsContinuation: lifecycleOf("I3", guardMutants.runsContinuation),
  withoutWrapper: lifecycleOf("I3", guardMutants.withoutWrapper),
  recordsThenForwards: lifecycleOf("I3", guardMutants.recordsThenForwards),
  releaseAfterCleanup: lifecycleOf("I4", lifeMutants.releaseAfterCleanup),
  neverReleases: lifecycleOf("I4", lifeMutants.neverReleases),
  releaseAtRequest: lifecycleOf("I4", lifeMutants.releaseAtRequest),
  privateQueue: lifecycleOf("I5", lifeMutants.privateQueue),
  exitBeforeCleanup: lifecycleOf("I6", lifeMutants.exitBeforeCleanup),
  omitDetached: lifecycleOf("I8", lifeMutants.omitDetached),
  omitInternal: lifecycleOf("I8", lifeMutants.omitInternal),
} as const satisfies Readonly<Record<string, LifecycleMutant>>;

/** A lifecycle mutant's name. */
export type LifecycleMutantName = keyof typeof lifecycleMutants;
