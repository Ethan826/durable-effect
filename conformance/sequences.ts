import { Brand } from "effect";
import fc from "fast-check";
import type {
  Event,
  FiberId,
  Outcome,
  Task,
  TaskId,
  Token,
} from "../src/adapter/Interface.ts";
import { makeAdapter } from "../src/adapter/Runtime.ts";
import { journal, program } from "./grammar.ts";
import type { Journal } from "./deliveries.ts";
import type { Program } from "./grammar.ts";
import { scriptedHost } from "./host.ts";
import type { LogEntry } from "./host.ts";
import { interpret } from "./interpret.ts";
import { coqLog, i4Breach, i6Breach, i7Breach, i8Breach } from "./logprops.ts";
import type { Variant } from "./mutants.ts";

// Arbitrary task sequences, by the owner's decision of 2026-11-22: the
// tasks a runtime may be sent, in any order, tasks the executor never
// sends included (a second `StartRoot`, deliveries for tokens no fiber
// awaits or for the wrong fiber, interrupts of fibers that have exited or
// never existed). Runtime.v's `I4`, `I6`, `I7` and `I8` quantify over
// every such sequence (`drive R A 0 0 (init R p seed) ts`).

/**
 * A task before it is resolved against the log so far. `known` picks
 * among the ids the log holds (queued tasks, started tokens, registered
 * fibers), exited or ended ones included; otherwise `pick` is the raw id,
 * which may name nothing.
 */
export type Step =
  | { readonly _tag: "StartRoot" }
  | {
    readonly _tag: "RunQueued";
    readonly pick: number;
    readonly known: boolean;
  }
  | {
    readonly _tag: "Deliver" | "DeliverCancel" | "DeliverDefect";
    readonly pick: number;
    readonly known: boolean;
    readonly wrongFiber: boolean;
    readonly outcome: Outcome;
  }
  | {
    readonly _tag: "RequestInterrupt";
    readonly pick: number;
    readonly known: boolean;
  };

const pick = fc.nat({ max: 40 });
const outcome: fc.Arbitrary<Outcome> = fc.record({
  _tag: fc.constantFrom("Value", "Failure"),
  value: fc.nat({ max: 2 }),
});

/** Mostly ids the log holds, so that runs get somewhere. */
const known = fc.constantFrom(true, true, true, false);

/**
 * The weights favour queued tasks and deliveries, which move a program
 * on, over starts and interrupts, which mostly stop it.
 */
const step: fc.Arbitrary<Step> = fc.oneof(
  { weight: 1, arbitrary: fc.constant({ _tag: "StartRoot" } as const) },
  {
    weight: 6,
    arbitrary: fc.record({ _tag: fc.constant("RunQueued"), pick, known }),
  },
  {
    weight: 4,
    arbitrary: fc.record({
      _tag: fc.constantFrom("Deliver", "DeliverCancel", "DeliverDefect"),
      pick, known, wrongFiber: fc.boolean(), outcome,
    }),
  },
  {
    weight: 1,
    arbitrary: fc.record({
      _tag: fc.constant("RequestInterrupt"), pick, known,
    }),
  },
);

/** One case: a program, its journal (for the answers), and the steps. */
export interface Sequence {
  readonly program: Program;
  readonly journal: Journal;
  readonly steps: ReadonlyArray<Step>;
}

/**
 * The cases: a program from the dossier's grammar and 1 to 60 steps,
 * after a leading `StartRoot` in three of every four.
 */
export const sequence: fc.Arbitrary<Sequence> = fc.record({
  program,
  journal,
  steps: fc.tuple(known, fc.array(step, {
    minLength: 1, maxLength: 60, size: "max",
  }))
    .map(([lead, rest]) => lead ? [{ _tag: "StartRoot" } as const, ...rest]
      : rest),
});

// Built from ids the log holds, or from a generated natural.
const fiberId = Brand.nominal<FiberId>();
const token = Brand.nominal<Token>();
const taskId = Brand.nominal<TaskId>();

/** The events a log holds, in order. */
export const eventsIn = (
  log: ReadonlyArray<LogEntry>,
): ReadonlyArray<Event> =>
  log.flatMap((entry) => entry._tag === "Emitted" ? [entry.event] : []);

/** The `index`-th of `ids`, wrapping round; none when there are none. */
const nth = <A>(ids: ReadonlyArray<A>, index: number): A | undefined =>
  ids[index % Math.max(ids.length, 1)];

const queued = (log: ReadonlyArray<LogEntry>) =>
  eventsIn(log).flatMap((event) => event._tag === "Queue" ? [event.task] : []);

/** The `Start` events a log holds. */
export const starts = (log: ReadonlyArray<LogEntry>) =>
  eventsIn(log).flatMap((event) => event._tag === "Start" ? [event] : []);

/** The fibers a log registers, in order. */
export const registered = (log: ReadonlyArray<LogEntry>) =>
  log.flatMap((entry) =>
    entry._tag === "Answered" && entry.question === "register"
      ? [entry.fiber]
      : []
  );

type DeliveryStep = Extract<Step, { readonly wrongFiber: boolean }>;

/** A delivery step as a task: a started token, or a raw one. */
const deliveryOf = (step: DeliveryStep, log: ReadonlyArray<LogEntry>) => {
  const start = step.known ? nth(starts(log), step.pick) : undefined;
  const owner = start?.fiber ?? step.pick;
  const fiber = fiberId(step.wrongFiber ? owner + 1 : owner);
  const tok = start?.token ?? token(step.pick);
  if (step._tag !== "Deliver") return { _tag: step._tag, fiber, token: tok };
  return { _tag: step._tag, fiber, token: tok, outcome: step.outcome };
};

/** A step as the task it stands for, given the log so far. */
export const resolve = (step: Step, log: ReadonlyArray<LogEntry>): Task => {
  if (step._tag === "StartRoot") return step;
  if (step._tag === "RunQueued") {
    const known = step.known ? nth(queued(log), step.pick) : undefined;
    return { _tag: "RunQueued", task: known ?? taskId(step.pick) };
  }
  if (step._tag === "RequestInterrupt") {
    const known = step.known ? nth(registered(log), step.pick) : undefined;
    return { _tag: "RequestInterrupt", fiber: known ?? fiberId(step.pick) };
  }
  return deliveryOf(step, log);
};

/** Runs a case's steps, each resolved against the log so far. */
export const drive = (
  { program: shape, journal: script, steps }: Sequence,
  make: Variant = makeAdapter,
): ReadonlyArray<LogEntry> => {
  const host = scriptedHost(script, { seed: 0 });
  const adapter = make(interpret(shape), 0, host);
  steps.forEach((one) => host.extend(adapter, resolve(one, host.log)));
  return host.log;
};

/** Runtime.v's four log properties of `Meets`, by name. */
export const sequenceChecks = {
  I4: i4Breach,
  I6: i6Breach,
  I7: i7Breach,
  I8: i8Breach,
} as const;

/** The first property a log breaks, with the breach; none when it holds. */
export const sequenceBreach = (
  log: ReadonlyArray<LogEntry>,
): string | undefined => {
  const coq = coqLog(log);
  return Object.entries(sequenceChecks).flatMap(([name, check]) => {
    const breach = check(coq);
    return breach === undefined ? [] : [`${name}: ${breach}`];
  })[0];
};
