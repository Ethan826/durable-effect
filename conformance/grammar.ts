import fc from "fast-check";
import type { Outcome } from "../src/adapter/Interface.ts";
import type { Journal } from "./host.ts";

/** A pure loop's step count; 2,049 and 5,000 cross `MaxOpsBeforeYield`. */
export type Count = 1 | 2 | 2049 | 5000;
/** One of the three kinds of durable `run` step. */
export type Kind = 0 | 1 | 2;
/** Which of the two shared refs or deferreds a statement uses. */
export type Slot = 0 | 1;

type Empty = Readonly<Record<never, never>>;
type Loop = { readonly count: Count };
type Caught = { readonly caught: boolean };
type Spaced = { readonly steps: 1 | 2 | 3; readonly jittered: boolean };
type OnFork = { readonly fiber: number };

/**
 * The fields of each statement kind, by tag: the dossier's grammar
 * (verification/dossier/scheduling-dossier.md, "The conformance suite:
 * grammar and bounds"). A `fiber` names a body in `Program.forks`.
 */
export interface StatementFields {
  readonly Run: { readonly kind: Kind };
  readonly Sleep: { readonly millis: 0 | 1 | 5 };
  readonly ClockRead: Empty;
  readonly RandomDraw: Empty;
  readonly YieldNow: Empty;
  readonly Loop: Loop;
  readonly Repeat: Loop;
  readonly Retry: Loop;
  readonly Timeout: Loop & { readonly millis: 1 | 5 };
  readonly RacePure: { readonly left: Count; readonly right: Count };
  readonly RaceDurable: Loop & { readonly kind: Kind };
  readonly Fail: Caught;
  readonly Die: Caught;
  readonly RetrySpaced: Spaced;
  readonly RepeatSpaced: Spaced;
  readonly Timed: Loop;
  readonly DateTimeNow: Empty;
  readonly Log: Empty;
  readonly FnSpan: Loop;
  readonly Call: Empty;
  readonly Never: Empty;
  readonly Deadlock: Empty;
  readonly All: {
    readonly counts: ReadonlyArray<Count>;
    readonly durable: boolean;
    readonly concurrency: 2 | "unbounded";
  };
  readonly ForEach: { readonly counts: ReadonlyArray<Count> };
  readonly Cached: Loop;
  readonly RefUpdate: { readonly ref: Slot };
  readonly RefGet: { readonly ref: Slot };
  readonly DeferredSucceed: { readonly deferred: Slot };
  readonly DeferredAwait: { readonly deferred: Slot };
  readonly QueueOffer: Empty;
  readonly QueueTake: Empty;
  readonly Fork: OnFork & { readonly detach: boolean };
  readonly Join: OnFork;
  readonly Interrupt: OnFork;
  readonly Poll: OnFork;
  readonly Uninterruptible: { readonly body: Sequence };
  readonly Ensuring: {
    readonly body: Sequence;
    readonly finalizer: Sequence;
  };
  readonly AcquireRelease: {
    readonly acquire: Sequence;
    readonly release: Sequence;
  };
}

/** A statement kind's tag. */
export type Tag = keyof StatementFields;

/** A statement of one of the kinds `K`, as plain data. */
export type Statement<K extends Tag = Tag> = {
  readonly [P in K]: { readonly _tag: P } & StatementFields[P];
}[K];

/** A sequence of statements, run one after another. */
export type Sequence = ReadonlyArray<Statement>;

/**
 * A program: the root fiber's body and up to three bodies the root and
 * other forks may fork. Body `i` forks, joins, interrupts or polls only
 * bodies after it, so no fiber waits on itself.
 */
export interface Program {
  readonly root: Sequence;
  readonly forks: ReadonlyArray<Sequence>;
}

const maxForks = 3;
const maxNesting = 3;
const count = fc.constantFrom<Count>(1, 2, 2049, 5000);
const kind = fc.constantFrom<Kind>(0, 1, 2);
const slot = fc.constantFrom<Slot>(0, 1);
const steps = fc.constantFrom<1 | 2 | 3>(1, 2, 3);
const spaced = { steps, jittered: fc.boolean() };

const only = <T extends Tag>(tag: T) => fc.constant({ _tag: tag });

/** Steps in one fiber with no sub-sequence: durable, time, failures. */
const sequentialLeaves = [
  fc.record({ _tag: fc.constant("Run"), kind }),
  fc.record({ _tag: fc.constant("Sleep"), millis: fc.constantFrom(0, 1, 5) }),
  only("ClockRead"), only("RandomDraw"), only("YieldNow"),
  fc.record({ _tag: fc.constant("Loop"), count }),
  fc.record({ _tag: fc.constant("Repeat"), count }),
  fc.record({ _tag: fc.constant("Retry"), count }),
  fc.record({
    _tag: fc.constant("Timeout"), count, millis: fc.constantFrom(1, 5),
  }),
  fc.record({ _tag: fc.constant("RacePure"), left: count, right: count }),
  fc.record({ _tag: fc.constant("RaceDurable"), count, kind }),
  fc.record({ _tag: fc.constant("Fail"), caught: fc.boolean() }),
  fc.record({ _tag: fc.constant("Die"), caught: fc.boolean() }),
  fc.record({ _tag: fc.constant("RetrySpaced"), ...spaced }),
  fc.record({ _tag: fc.constant("RepeatSpaced"), ...spaced }),
  fc.record({ _tag: fc.constant("Timed"), count }),
  only("DateTimeNow"), only("Log"),
  fc.record({ _tag: fc.constant("FnSpan"), count }),
  only("Call"), only("Never"), only("Deadlock"),
] satisfies ReadonlyArray<fc.Arbitrary<Statement>>;

/** Immediate forks, caching, and the shared refs, deferreds and queue. */
const sharedLeaves = [
  fc.record({
    _tag: fc.constant("All"),
    counts: fc.array(count, { minLength: 1, maxLength: 3 }),
    durable: fc.boolean(),
    concurrency: fc.constantFrom<2 | "unbounded">(2, "unbounded"),
  }),
  fc.record({
    _tag: fc.constant("ForEach"),
    counts: fc.array(count, { minLength: 1, maxLength: 8 }),
  }),
  fc.record({ _tag: fc.constant("Cached"), count }),
  fc.record({ _tag: fc.constant("RefUpdate"), ref: slot }),
  fc.record({ _tag: fc.constant("RefGet"), ref: slot }),
  fc.record({ _tag: fc.constant("DeferredSucceed"), deferred: slot }),
  fc.record({ _tag: fc.constant("DeferredAwait"), deferred: slot }),
  only("QueueOffer"), only("QueueTake"),
] satisfies ReadonlyArray<fc.Arbitrary<Statement>>;

/** The statements with no sub-sequence and no fork target. */
const plainLeaves = [...sequentialLeaves, ...sharedLeaves];

/** The statements on a fork body after `owner`; none when there is none. */
const forkLeaves = (owner: number, forks: number) => {
  if (owner + 1 >= forks) return [];
  const fiber = fc.integer({ min: owner + 1, max: forks - 1 });
  return [
    fc.record({ _tag: fc.constant("Fork"), fiber, detach: fc.boolean() }),
    fc.record({ _tag: fc.constant("Join"), fiber }),
    fc.record({ _tag: fc.constant("Interrupt"), fiber }),
    fc.record({ _tag: fc.constant("Poll"), fiber }),
  ] satisfies ReadonlyArray<fc.Arbitrary<Statement>>;
};

/** Where a statement sits: its body's owner, the fork count, levels left. */
interface Place {
  readonly owner: number;
  readonly forks: number;
  readonly levels: number;
}

const finalizerLength = { minLength: 1, maxLength: 2 };

/** The statements holding sub-sequences, one level further in. */
const containers = (inner: Place) => {
  const body = sequence(inner);
  const finalizer = fc.array(statement(inner), finalizerLength);
  return [
    fc.record({ _tag: fc.constant("Uninterruptible"), body }),
    fc.record({ _tag: fc.constant("Ensuring"), body, finalizer }),
    fc.record({
      _tag: fc.constant("AcquireRelease"), acquire: body, release: finalizer,
    }),
  ] satisfies ReadonlyArray<fc.Arbitrary<Statement>>;
};

/** Any statement that fits in `place`; containers only above level 1. */
const statement = (place: Place): fc.Arbitrary<Statement> => {
  const inner = { ...place, levels: place.levels - 1 };
  const nested = place.levels > 1 ? containers(inner) : [];
  return fc.oneof(
    ...plainLeaves,
    ...forkLeaves(place.owner, place.forks),
    ...nested,
  );
};

/** One to six statements that fit in `place`. */
const sequence = (place: Place): fc.Arbitrary<Sequence> =>
  fc.array(statement(place), { minLength: 1, maxLength: 6 });

const bodyOf = (forks: number) => (owner: number) =>
  sequence({ owner, forks, levels: maxNesting });

const programWith = (forks: number): fc.Arbitrary<Program> =>
  fc.record({
    root: bodyOf(forks)(-1),
    forks: fc.tuple(...Array.from({ length: forks }, (_, at) =>
      bodyOf(forks)(at)
    )),
  });

/**
 * The dossier's programs: a root body and up to three fork bodies, each
 * one to six statements, nested at most three levels deep.
 */
export const program: fc.Arbitrary<Program> = fc
  .integer({ min: 0, max: maxForks })
  .chain(programWith);

const outcome: fc.Arbitrary<Outcome> = fc.oneof(
  fc.record({ _tag: fc.constant("Value"), value: fc.constantFrom(0, 1, 2) }),
  fc.record({ _tag: fc.constant("Failure"), value: fc.constantFrom(0, 1, 2) }),
);

/**
 * The dossier's journals: one to eight outcomes, each a `Value` or a
 * `Failure` of 0, 1 or 2, and a cancel absent or before one of the first
 * four notifications.
 */
export const journal: fc.Arbitrary<Journal> = fc.record({
  outcomes: fc.array(outcome, { minLength: 1, maxLength: 8 }),
  cancelBefore: fc.option(fc.constantFrom(0, 1, 2, 3), { nil: undefined }),
});
