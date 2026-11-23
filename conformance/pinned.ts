import type { Journal } from "./deliveries.ts";
import type { Program, Sequence, Statement } from "./grammar.ts";

// I9's pinned cases (dossier, "Runs"): programs of the grammar that each
// run more than 2,048 x 9 operations in one task, which refuted the old
// per-task bound. The suite always runs them.

const statementsPerLevel = 6;
const finalizerLength = 2;
const groupSize = statementsPerLevel + finalizerLength;

/** Up to eight statements as one: `Ensuring` of six and two, in order. */
const group = (statements: Sequence): Statement =>
  statements.length <= statementsPerLevel
    ? { _tag: "Uninterruptible", body: statements }
    : {
      _tag: "Ensuring",
      body: statements.slice(0, statementsPerLevel),
      finalizer: statements.slice(statementsPerLevel),
    };

const chunks = (statements: Sequence): ReadonlyArray<Sequence> =>
  Array.from(
    { length: Math.ceil(statements.length / groupSize) },
    (_, at) => statements.slice(at * groupSize, (at + 1) * groupSize),
  );

/**
 * Up to 384 statements as one body of the grammar, run in order: at most
 * six top-level statements, each `Ensuring` (body six, finalizer two)
 * nested twice, so three levels. Ported from the I9 derivation's probe.
 */
export const pack = (statements: Sequence): Sequence => {
  if (statements.length <= statementsPerLevel) return statements;
  const inner = chunks(statements).map(group);
  return inner.length <= statementsPerLevel
    ? inner
    : chunks(inner).map(group);
};

const forkOf = (fiber: number): Statement =>
  ({ _tag: "Fork", fiber, detach: false });
const awaitOf = (deferred: 0 | 1): Statement =>
  ({ _tag: "DeferredAwait", deferred });
const succeedOf = (deferred: 0 | 1): Statement =>
  ({ _tag: "DeferredSucceed", deferred });
const forEach8: Statement = {
  _tag: "ForEach",
  counts: [5000, 5000, 5000, 5000, 5000, 5000, 5000, 5000],
};
/** A race whose large side loses: a full slice runs inline (I9). */
const losingRace: Statement = { _tag: "RacePure", left: 5000, right: 1 };
const races = (count: number): Sequence =>
  Array.from({ length: count }, () => losingRace);

/** One `Value` 0 for every run, and no cancel. */
export const pinnedJournal: Journal = {
  outcomes: [{ _tag: "Value", value: 0 }],
  cancelBefore: undefined,
};

/** One deferred wakes two forks inline, each running a forEach of 8. */
const twoWoken: Program = {
  root: [
    forkOf(0), forkOf(1), { _tag: "YieldNow" }, { _tag: "Loop", count: 1 },
    succeedOf(0), { _tag: "Join", fiber: 0 },
  ],
  forks: [[awaitOf(0), forEach8], [awaitOf(0), forEach8]],
};

const waiter = pack([awaitOf(0), ...races(190), awaitOf(1), ...races(191),
  forEach8]);

/** chain2: every body runs losing races between wakes (I9 derivation). */
const chain2: Program = {
  root: pack([forkOf(0), forkOf(1), forkOf(2), awaitOf(0), ...races(190),
    awaitOf(1), ...races(188), forEach8]),
  forks: [waiter, waiter, pack([succeedOf(0), ...races(2), succeedOf(1),
    ...races(290), forEach8])],
};

/** The pinned cases, by name. */
export const pinnedCases: Readonly<Record<string, Program>> = {
  twoWoken,
  chain2,
};
