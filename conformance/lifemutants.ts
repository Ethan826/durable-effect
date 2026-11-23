import { Effect, Exit, Fiber } from "effect";
import type {
  Event,
  FiberId,
  Host,
  RootExit,
  Task,
  Token,
} from "../src/adapter/Interface.ts";
import { makeAdapter } from "../src/adapter/Runtime.ts";
import { loopDepth } from "./census.ts";
import type { Variant } from "./mutants.ts";

// The mutants #37's table lists for I4, I5, I6 and I8. Each wraps the
// adapter, its host or its program; none changes src/.

/** Builds a host for the adapter, and a task runner around it. */
type Around = (host: Host) => {
  readonly host: Host;
  readonly before?: (task: Task, run: (task: Task) => void) => void;
  readonly after?: () => void;
};

/** The adapter with a host and a task runner made by `around`. */
const wrapped = (around: Around): Variant => (program, seed, outer) => {
  const { host, before, after } = around(outer);
  const inner = makeAdapter(program, seed, host);
  const runTask = (task: Task) => {
    before?.(task, inner.runTask);
    inner.runTask(task);
    after?.();
  };
  return { runTask };
};

/** A host whose events pass through `filter` first. */
const filtering = (host: Host, filter: (event: Event) => boolean): Host => ({
  ...host,
  emit: (event) => {
    if (filter(event)) host.emit(event);
  },
});

/** Keeps back the events `holds` picks in `held`; passes the rest. */
const holding = (held: Event[], holds: (event: Event) => boolean) =>
  (event: Event) => {
    if (!holds(event)) return true;
    held.push(event);
    return false;
  };

const isRelease = (event: Event) => event._tag === "Release";

/** I4: releases are held until the task has run, after the cleanup. */
const releaseAfterCleanup = wrapped((host) => {
  const held: Event[] = [];
  return {
    host: filtering(host, holding(held, isRelease)),
    after: () => held.splice(0).forEach(host.emit),
  };
});

/** I4: no release is ever reported. */
const neverReleases = wrapped((host) => ({
  host: filtering(host, (event) => event._tag !== "Release"),
}));

/**
 * I4: on an interruption request, a release for each await of the fiber,
 * masked or not; the adapter's own release for it is dropped later.
 */
const releaseAtRequest = wrapped((host) => {
  const awaits = new Map<Token, FiberId>();
  const early = new Set<Token>();
  const keep = (event: Event) => {
    if (event._tag === "Start") awaits.set(event.token, event.fiber);
    if (event._tag !== "Release") return true;
    awaits.delete(event.token);
    return !early.delete(event.token);
  };
  const before = (task: Task) => {
    if (task._tag !== "RequestInterrupt") return;
    [...awaits].filter(([, fiber]) => fiber === task.fiber)
      .forEach(([token, fiber]) => {
        awaits.delete(token);
        early.add(token);
        host.emit({ _tag: "Release", fiber, token });
      });
  };
  return { host: filtering(host, keep), before };
});

/** I5: every other queued task is kept back and run before the next. */
const privateQueue = wrapped((host) => {
  const hidden: Event[] = [];
  const odd = (event: Event) => event._tag === "Queue" && event.task % 2 === 1;
  const before = (_: Task, run: (task: Task) => void) =>
    hidden.splice(0).forEach((event) => {
      if (event._tag === "Queue") run({ _tag: "RunQueued", task: event.task });
    });
  return { host: filtering(host, holding(hidden, odd)), before };
});

const earlyExit = (exit: Exit.Exit<unknown, unknown>): RootExit =>
  Exit.isSuccess(exit) ? { _tag: "Success", value: 0 } :
    Exit.hasInterrupts(exit) ? { _tag: "Interrupted" } : { _tag: "Defect" };

/**
 * I6: the root's exit is reported from inside the root as its program
 * ends, before the root fiber's own cleanup (its children's interruption
 * and its exit); the adapter's report is dropped.
 */
const exitBeforeCleanup: Variant = (program, seed, outer) => {
  const host = filtering(outer, (event) => event._tag !== "RootExit");
  const report = (exit: Exit.Exit<unknown, unknown>) =>
    Effect.sync(() => outer.emit({ _tag: "RootExit", exit: earlyExit(exit) }));
  return makeAdapter(Effect.onExit(program, report), seed, host);
};

/** Whether the fiber registering now is one the registry leaves out. */
type Omits = (first: boolean) => boolean;

/**
 * I8: the fibers `omits` picks are never registered and their exits are
 * not reported; their other entries still reach the host.
 */
const omitting = (omits: Omits) => wrapped((host) => {
  const hidden = new Set<FiberId>();
  const registry = { count: 0 };
  const register = (fiber: FiberId) => {
    if (!omits(registry.count++ === 0)) return host.register(fiber);
    hidden.add(fiber);
    return false;
  };
  const keep = (event: Event) =>
    event._tag !== "FiberExited" || !hidden.has(event.fiber);
  return { host: { ...filtering(host, keep), register } };
});

/** A fiber started inside another's run loop: `forEach`, `race`, ... */
const isInternal = () => loopDepth() >= 2;

/** A fiber with no parent that is not the root: `forkDetach`. */
const isDetached = (first: boolean) => {
  const current = Fiber.getCurrent();
  return !first && !isInternal() && current !== undefined &&
    Reflect.get(current, "_parent") === undefined;
};

/** I4, I5, I6 and I8's mutants, by name. */
export const lifeMutants = {
  releaseAfterCleanup,
  neverReleases,
  releaseAtRequest,
  privateQueue,
  exitBeforeCleanup,
  omitDetached: omitting(isDetached),
  omitInternal: omitting(isInternal),
} as const;
