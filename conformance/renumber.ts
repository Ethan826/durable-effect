import { Brand, Match } from "effect";
import type { Effect } from "effect";
import type { Durable } from "../src/adapter/Durable.ts";
import type {
  AdapterRuntime,
  Event,
  FiberId,
  Host,
  Task,
  Token,
} from "../src/adapter/Interface.ts";
import { makeAdapter } from "../src/adapter/Runtime.ts";

/** How a renumbering mutant gives out the identities the host sees. */
interface Numbering {
  readonly next: () => FiberId;
  readonly exited: (fiber: FiberId) => void;
}

// Counters only count up from zero, so each value is a natural number.
const fiberId = Brand.nominal<FiberId>();

// Shared by every adapter this process makes: the defect being tested.
const processWide = { next: 0 };

/** The three ways I7's mutants number fibers. */
const numberings = {
  processCounter: (): Numbering => ({
    next: () => fiberId(processWide.next++),
    exited: () => {},
  }),
  sameIdentity: (): Numbering => ({
    next: () => fiberId(0),
    exited: () => {},
  }),
  reuseExited: (): Numbering => {
    const free: FiberId[] = [];
    const counter = { next: 0 };
    return {
      next: () => free.pop() ?? fiberId(counter.next++),
      exited: (fiber) => {
        free.push(fiber);
      },
    };
  },
} as const;

/** The two directions between the adapter's ids and the host's. */
interface Ids {
  readonly numbering: Numbering;
  readonly toPublic: Map<FiberId, FiberId>;
  readonly toReal: Map<FiberId, FiberId>;
  /** The adapter's fiber for each token, from its `Start`. */
  readonly owners: Map<Token, FiberId>;
}

const publicOf = (ids: Ids, real: FiberId) => ids.toPublic.get(real) ?? real;
const realOf = (ids: Ids, shown: FiberId) => ids.toReal.get(shown) ?? shown;

/** An event as the host sees it, noting starts and exits on the way. */
const outward = (ids: Ids) => (event: Event): Event =>
  Match.value(event).pipe(Match.tagsExhaustive({
    Start: (start) => {
      ids.owners.set(start.token, start.fiber);
      return { ...start, fiber: publicOf(ids, start.fiber) };
    },
    Release: (release) => ({ ...release, fiber: publicOf(ids, release.fiber) }),
    FiberExited: (exited) => {
      const shown = publicOf(ids, exited.fiber);
      ids.numbering.exited(shown);
      return { ...exited, fiber: shown };
    },
    Queue: (queued) => queued,
    RootExit: (exit) => exit,
  }));

const delivered = (ids: Ids) =>
  <T extends { readonly fiber: FiberId; readonly token: Token }>(task: T) =>
    ({
      ...task,
      fiber: ids.owners.get(task.token) ?? realOf(ids, task.fiber),
    });

/** A task as the adapter sees it: the host's ids taken back. */
const inward = (ids: Ids) => (task: Task): Task =>
  Match.value(task).pipe(Match.tagsExhaustive({
    StartRoot: (start) => start,
    RunQueued: (queued) => queued,
    Deliver: delivered(ids),
    DeliverCancel: delivered(ids),
    DeliverDefect: delivered(ids),
    RequestInterrupt: (request) =>
      ({ ...request, fiber: realOf(ids, request.fiber) }),
  }));

/** The host the adapter talks to: every fiber id renumbered. */
const renumberingHost = (ids: Ids, host: Host): Host => ({
  ...host,
  register: (real) => {
    const shown = ids.numbering.next();
    ids.toPublic.set(real, shown);
    ids.toReal.set(shown, real);
    return host.register(shown);
  },
  clock: (real) => host.clock(publicOf(ids, real)),
  draw: (real) => host.draw(publicOf(ids, real)),
  foreign: (kind, real) => host.foreign(kind, publicOf(ids, real)),
  emit: (event) => host.emit(outward(ids)(event)),
});

/**
 * I7's mutants: the adapter, with the fiber ids the host sees given out by
 * a process-wide counter, as one id for every fiber, or reusing the id of
 * a fiber that has exited. Tasks from the host are mapped back, a delivery
 * by the fiber that started its token.
 */
export const renumbered = (kind: keyof typeof numberings) =>
  <A, E>(
    program: Effect.Effect<A, E, Durable>,
    seed: number,
    host: Host,
  ): AdapterRuntime => {
    const ids: Ids = {
      numbering: numberings[kind](),
      toPublic: new Map(),
      toReal: new Map(),
      owners: new Map(),
    };
    const inner = makeAdapter(program, seed, renumberingHost(ids, host));
    return { runTask: (task) => inner.runTask(inward(ids)(task)) };
  };
