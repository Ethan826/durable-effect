import { Effect, Exit, Match, Option, Schema } from "effect";
import { deliver, Durable, makeDurable } from "./Durable.ts";
import { registration, requestInterrupt } from "./Fibers.ts";
import type {
  AdapterRuntime,
  Host,
  RootExit,
  Task,
  TaskId,
} from "./Interface.ts";
import { deterministicScheduler } from "./Scheduler.ts";
import { makeState } from "./State.ts";
import type { AdapterState } from "./State.ts";

const decodeNatural = Schema.decodeUnknownOption(Schema.Natural);

/**
 * The model's abstract natural for a value: the value itself when it decodes
 * as a natural, otherwise 0. The model never looks inside a value.
 */
const abstractNatural = (value: unknown): number =>
  Option.getOrElse(decodeNatural(value), () => 0);

const success = (value: unknown): RootExit => ({
  _tag: "Success",
  value: abstractNatural(value),
});
const failure = (value: unknown): RootExit => ({
  _tag: "Failure",
  value: abstractNatural(value),
});

/** The cause of a failed exit, read in the order fail, die, interrupt. */
const failed = <A, E>(exit: Exit.Exit<A, E>): RootExit =>
  Option.match(Exit.findErrorOption(exit), {
    onSome: failure,
    onNone: (): RootExit =>
      Exit.hasDies(exit) ? { _tag: "Defect" } : { _tag: "Interrupted" },
  });

/** Effect's exit as the interface's `RootExit`. */
const toRootExit = <A, E>(exit: Exit.Exit<A, E>): RootExit =>
  Exit.isSuccess(exit) ? success(exit.value) : failed(exit);

/**
 * Forks the program with the `Durable` service. The root registers in its
 * first `shouldYield`, so its `FiberExited` observer is added before this
 * one and fires first.
 */
const startRoot = <A, E>(
  state: AdapterState,
  host: Host,
  program: Effect.Effect<A, E, Durable>,
) => {
  const scheduler = deterministicScheduler(state, host);
  const provided = Effect.provideService(
    program,
    Durable,
    makeDurable(state, host),
  );
  const root = Effect.runFork(provided, { scheduler });
  root.addObserver((exit) => {
    host.emit({ _tag: "RootExit", exit: toRootExit(exit) });
  });
};

/** Runs a queued thunk once; an unknown task does nothing. */
const runQueued = (state: AdapterState, task: TaskId) => {
  const thunk = state.tasks.get(task);
  state.tasks.delete(task);
  thunk?.();
};

/**
 * Builds the runtime side of the interface for one handler run. `StartRoot`
 * forks the program the first time and does nothing after; `RunQueued` runs
 * a stored thunk; the three deliveries answer an await; `RequestInterrupt`
 * interrupts a fiber. `seed` is for the deterministic services (Task 9).
 */
export const makeAdapter = <A, E>(
  program: Effect.Effect<A, E, Durable>,
  _seed: number,
  host: Host,
): AdapterRuntime => {
  const state = makeState();
  state.register = registration(state, host);
  let started = false;
  // The flag is set first, so a StartRoot sent while the root's first slice
  // is still running cannot start it a second time.
  const startOnce = () => {
    if (started) return;
    started = true;
    startRoot(state, host, program);
  };
  const runTask = (task: Task) =>
    Match.value(task).pipe(Match.tagsExhaustive({
      StartRoot: startOnce,
      RunQueued: (queued) => runQueued(state, queued.task),
      Deliver: (delivery) => deliver(state, delivery),
      DeliverCancel: (delivery) => deliver(state, delivery),
      DeliverDefect: (delivery) => deliver(state, delivery),
      RequestInterrupt: (request) => requestInterrupt(state, request.fiber),
    }));
  return { runTask };
};
