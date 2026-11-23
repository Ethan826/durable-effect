import { Match } from "effect";
import type {
  AdapterRuntime,
  Event,
  FiberId,
  GlobalSource,
  Host,
  Outcome,
  Task,
  TaskId,
  Token,
} from "../src/adapter/Interface.ts";

/**
 * A scripted journal. The `n`-th `Run` token, counted from 0 in token
 * order, gets `outcomes[n mod outcomes.length]`, so `Run` tokens take the
 * outcomes in order and start again from the first when they run out. A
 * `Sleep` token always gets `Value` 0: a real executor completes or
 * cancels a sleep and never fails it. `cancelBefore`, when
 * set to `k`, sends a `DeliverCancel` in place of the `k`-th notification
 * (counted from 0), to the fiber awaiting at that point.
 */
export interface Journal {
  readonly outcomes: ReadonlyArray<Outcome>;
  readonly cancelBefore: number | undefined;
}

/** How the scripted host answers draws: from this seed. */
export interface HostOptions {
  readonly seed: number;
}

/** One entry of the scripted host's log, in the order it happened. */
export type LogEntry =
  | { readonly _tag: "Sent"; readonly task: Task }
  | { readonly _tag: "Emitted"; readonly event: Event }
  | {
    readonly _tag: "Answered";
    readonly question: "clock" | "draw" | "register";
    readonly fiber: FiberId;
    readonly answer: number | boolean;
  }
  | {
    readonly _tag: "Foreign";
    readonly kind: "resume" | "interrupt";
    readonly fiber: FiberId;
  }
  | { readonly _tag: "Global"; readonly source: GlobalSource }
  | { readonly _tag: "Blocked" };

/** A host that also runs the adapter and keeps a log of everything. */
export type ScriptedHost = Host & {
  readonly log: ReadonlyArray<LogEntry>;
  readonly run: (adapter: AdapterRuntime) => void;
};

/** An awaited token's fiber, and its place among `Run` tokens if a run. */
interface Awaited {
  readonly fiber: FiberId;
  readonly run: number | undefined;
}

interface HostState {
  readonly log: LogEntry[];
  readonly queue: TaskId[];
  readonly awaited: Map<Token, Awaited>;
  readonly live: Set<FiberId>;
  delivered: number;
  runs: number;
  random: number;
  slice: boolean;
  closing: boolean;
  interruptsSent: boolean;
  cancelled: boolean;
}

/** Numerical Recipes' 32-bit LCG (Press et al., 2nd ed., §7.1, ranqd1). */
const lcgMultiplier = 1664525;
const lcgIncrement = 1013904223;
const nextRandom = (current: number): number =>
  (Math.imul(current, lcgMultiplier) + lcgIncrement) >>> 0;

const valueZero: Outcome = { _tag: "Value", value: 0 };

/** Numbers a `Run` token among the runs; a `Sleep` token gets none. */
const awaitedOf = (
  state: HostState,
  start: Extract<Event, { readonly _tag: "Start" }>,
): Awaited => {
  if (start.op._tag === "Sleep") return { fiber: start.fiber, run: undefined };
  return { fiber: start.fiber, run: state.runs++ };
};

/** What the host learns from an event: awaits, queue, fibers, closing. */
const observe = (state: HostState) => (event: Event) => {
  state.log.push({ _tag: "Emitted", event });
  Match.value(event).pipe(Match.tagsExhaustive({
    Start: (start) =>
      state.awaited.set(start.token, awaitedOf(state, start)),
    Release: (release) => state.awaited.delete(release.token),
    Queue: (queued) => state.queue.push(queued.task),
    FiberExited: (exited) => state.live.delete(exited.fiber),
    RootExit: () => {
      state.closing = true;
    },
  }));
};

/** Logs an answer to a question and returns it. */
const answer = <A extends number | boolean>(
  state: HostState,
  question: "clock" | "draw" | "register",
  fiber: FiberId,
  value: A,
): A => {
  state.log.push({ _tag: "Answered", question, fiber, answer: value });
  return value;
};

const draw = (state: HostState) => (fiber: FiberId) => {
  state.random = nextRandom(state.random);
  return answer(state, "draw", fiber, state.random);
};

const register = (state: HostState) => (fiber: FiberId) => {
  state.live.add(fiber);
  return answer(state, "register", fiber, state.closing);
};

/** Sends one task, inside a slice, and logs it first. */
const sender = (state: HostState, adapter: AdapterRuntime) =>
  (task: Task) => {
    state.log.push({ _tag: "Sent", task });
    state.slice = true;
    adapter.runTask(task);
    state.slice = false;
  };

/** The awaited token with the lowest number, with what awaits it. */
const oldestAwait = (state: HostState) =>
  [...state.awaited].sort(([left], [right]) => left - right)[0];

/**
 * Answers the oldest await: with the scripted cancel if it is due now,
 * otherwise with the token's outcome. The await is forgotten first, since
 * the adapter reports no `Release` for an await it resumes.
 */
const deliverTo = (
  state: HostState,
  journal: Journal,
  send: (task: Task) => void,
) => ([token, { fiber, run }]: readonly [Token, Awaited]) => {
  state.awaited.delete(token);
  const cancelDue = !state.cancelled &&
    state.delivered === journal.cancelBefore;
  if (cancelDue) {
    state.cancelled = true;
    return send({ _tag: "DeliverCancel", fiber, token });
  }
  state.delivered += 1;
  send({ _tag: "Deliver", fiber, token, outcome: outcomeOf(journal, run) });
};

/** A run's scripted outcome; `Value` 0 for a sleep. */
const outcomeOf = (journal: Journal, run: number | undefined): Outcome =>
  run === undefined
    ? valueZero
    : journal.outcomes[run % journal.outcomes.length] ?? valueZero;

/** Once the root has exited, asks every live fiber to stop, lowest first. */
const interruptLive = (state: HostState, send: (task: Task) => void) => {
  state.interruptsSent = true;
  const live = [...state.live].sort((left, right) => left - right);
  live.forEach((fiber) => send({ _tag: "RequestInterrupt", fiber }));
};

/**
 * One step of the run: interrupts on entering closing, then the next queued
 * task, then a delivery. Answers `false` when the run is over: closing with
 * an empty queue, or nothing queued or awaited before the root exits.
 */
const step = (
  state: HostState,
  journal: Journal,
  send: (task: Task) => void,
): boolean => {
  if (state.closing && !state.interruptsSent) {
    interruptLive(state, send);
    return true;
  }
  const next = state.queue.shift();
  if (next !== undefined) {
    send({ _tag: "RunQueued", task: next });
    return true;
  }
  if (state.closing) return false;
  const oldest = oldestAwait(state);
  if (oldest === undefined) state.log.push({ _tag: "Blocked" });
  else deliverTo(state, journal, send)(oldest);
  return oldest !== undefined;
};

const freshState = (options: HostOptions): HostState => ({
  log: [],
  queue: [],
  awaited: new Map(),
  live: new Set(),
  delivered: 0,
  runs: 0,
  random: options.seed >>> 0,
  slice: false,
  closing: false,
  interruptsSent: false,
  cancelled: false,
});

/**
 * A stand-in for the executor, not the executor. `run` sends `StartRoot`,
 * then runs queued tasks first in, first out, whatever their priority. When
 * the queue is empty it answers the oldest awaited token: a run from the
 * journal, a sleep with `Value` (see {@link Journal}). When nothing is
 * awaited either, and the root has not exited, it logs `Blocked` and
 * stops. Once the root exits it is closing: `register` answers true,
 * every live fiber gets a `RequestInterrupt`, nothing more is delivered,
 * and it stops when the queue is empty. The clock answers the number of
 * notifications delivered so far, in milliseconds; draws come from an LCG
 * started at the seed. `inSlice` is true only inside `runTask`.
 */
export const scriptedHost = (
  journal: Journal,
  options: HostOptions,
): ScriptedHost => {
  const state = freshState(options);
  const run = (adapter: AdapterRuntime) => {
    const send = sender(state, adapter);
    send({ _tag: "StartRoot" });
    while (step(state, journal, send));
  };
  return {
    log: state.log,
    run,
    emit: observe(state),
    clock: (fiber) => answer(state, "clock", fiber, state.delivered),
    draw: draw(state),
    register: register(state),
    inSlice: () => state.slice,
    foreign: (kind, fiber) => state.log.push({ _tag: "Foreign", kind, fiber }),
    noteGlobal: (source) => state.log.push({ _tag: "Global", source }),
  };
};
