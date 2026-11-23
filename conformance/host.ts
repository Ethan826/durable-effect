import { Match } from "effect";
import type {
  AdapterRuntime,
  Event,
  FiberId,
  GlobalSource,
  Host,
  Task,
} from "../src/adapter/Interface.ts";
import { freshDeliveries, nextNotification, noteStart } from "./deliveries.ts";
import type { Deliveries, Journal, Start } from "./deliveries.ts";

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

/**
 * The host's state: the awaits it will answer, the tasks it will send, in
 * order, and the fibers still live.
 */
interface HostState extends Deliveries {
  readonly log: LogEntry[];
  readonly queue: Task[];
  readonly live: Set<FiberId>;
  random: number;
  slice: boolean;
  closing: boolean;
  interruptsSent: boolean;
}

/** Numerical Recipes' 32-bit LCG (Press et al., 2nd ed., §7.1, ranqd1). */
const lcgMultiplier = 1664525;
const lcgIncrement = 1013904223;
const nextRandom = (current: number): number =>
  (Math.imul(current, lcgMultiplier) + lcgIncrement) >>> 0;

/**
 * An operation started while closing is refused: the host queues a
 * `DeliverDefect` for it (#37 X6.3). Otherwise the host will answer it.
 */
const onStart = (state: HostState, start: Start) => {
  if (!state.closing) return noteStart(state, start);
  const { fiber, token } = start;
  state.queue.push({ _tag: "DeliverDefect", fiber, token });
};

/** What the host learns from an event: awaits, queue, fibers, closing. */
const observe = (state: HostState) => (event: Event) => {
  state.log.push({ _tag: "Emitted", event });
  Match.value(event).pipe(Match.tagsExhaustive({
    Start: (start) => onStart(state, start),
    Release: (release) => state.awaited.delete(release.token),
    Queue: (queued) =>
      state.queue.push({ _tag: "RunQueued", task: queued.task }),
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

/** Once the root has exited, asks every live fiber to stop, lowest first. */
const interruptLive = (state: HostState, send: (task: Task) => void) => {
  state.interruptsSent = true;
  const live = [...state.live].sort((left, right) => left - right);
  live.forEach((fiber) => send({ _tag: "RequestInterrupt", fiber }));
};

/** The next queued task, else a notification unless closing. */
const nextTask = (state: HostState, journal: Journal): Task | undefined =>
  state.queue.shift() ??
    (state.closing ? undefined : nextNotification(state, journal));

/**
 * One step of the run: interrupts on entering closing, then the next queued
 * task, then a notification. Answers `false` when the run is over: closing
 * with an empty queue, or nothing queued and nothing to notify before the
 * root exits. A refused operation's `DeliverDefect` is queued, so closing
 * answers it before it stops.
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
  const next = nextTask(state, journal);
  if (next !== undefined) {
    send(next);
    return true;
  }
  if (!state.closing) state.log.push({ _tag: "Blocked" });
  return false;
};

const freshState = (options: HostOptions): HostState => ({
  ...freshDeliveries(),
  log: [],
  queue: [],
  live: new Set(),
  random: options.seed >>> 0,
  slice: false,
  closing: false,
  interruptsSent: false,
});

/**
 * A stand-in for the executor, not the executor. `run` sends `StartRoot`,
 * then runs queued tasks first in, first out, whatever their priority. When
 * the queue is empty it answers the oldest awaited token it can: a run
 * from the journal, a finite sleep with `Value`, never a sleep `Forever`
 * (see {@link Journal}). When it can answer nothing, and the root has not
 * exited, it logs `Blocked` and stops. Once the root exits it is closing:
 * `register` answers true, every live fiber gets a `RequestInterrupt`,
 * nothing more is delivered, an operation started now gets a
 * `DeliverDefect`, and it stops when the queue is empty. The clock
 * answers the number of notifications delivered so far, in milliseconds;
 * draws come from an LCG started at the seed. `inSlice` is true only
 * inside `runTask`.
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
