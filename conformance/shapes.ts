import type { LogEntry } from "./host.ts";
import type { Program, Sequence, Statement } from "./grammar.ts";
import type { LifecycleRun } from "./lifecycle.ts";

// The cases #37's "Conformance test" column names for I4, I5 and I6,
// counted in the runs so that a floor can require each one. Where the log
// cannot tell a case apart, the count is of runs whose program holds the
// shape and whose log shows the moment it matters (a root exit). I8's
// cases, a fiber masked when it first runs during closing, are beyond the
// grammar (grammar.ts:59: a `Fork` has no mask of its own), so they are
// pinned cases in closing.ts.

/** The counts, one per named case. */
export interface ShapeScans {
  /** I4: programs with a race of a durable operation against pure work. */
  readonly durableRaces: number;
  /** I4: programs with a timeout around pure work. */
  readonly pureTimeouts: number;
  /** I5: fibers woken inside another fiber's loop (census). */
  readonly inlineWakes: number;
  /** I5: programs that fork a body that awaits a deferred. */
  readonly blockedChildren: number;
  /** I6: runs whose root exited past a finalizer that may yield. */
  readonly yieldingFinalizers: number;
}

/** The sub-sequences a statement holds, in order. */
const inner = (statement: Statement): ReadonlyArray<Sequence> => {
  if (statement._tag === "Uninterruptible") return [statement.body];
  if (statement._tag === "Ensuring") {
    return [statement.body, statement.finalizer];
  }
  return statement._tag === "AcquireRelease"
    ? [statement.acquire, statement.release]
    : [];
};

type Test = (statement: Statement) => boolean;

/** Every statement in `body`, at any depth, that meets `test`. */
const collect = (body: Sequence, test: Test): ReadonlyArray<Statement> =>
  body.flatMap((statement) => [
    ...(test(statement) ? [statement] : []),
    ...inner(statement).flatMap((sub) => collect(sub, test)),
  ]);

/** Whether any statement in `body`, at any depth, meets `test`. */
const holds = (body: Sequence, test: Test) => collect(body, test).length > 0;

/** A finalizer's statements: those an `ensuring` or a release runs. */
const finalizersIn = (body: Sequence): ReadonlyArray<Sequence> =>
  body.flatMap((one) => [
    ...(one._tag === "Ensuring" ? [one.finalizer] : []),
    ...(one._tag === "AcquireRelease" ? [one.release] : []),
    ...inner(one).flatMap(finalizersIn),
  ]);

const bodies = (program: Program) => [program.root, ...program.forks];

const anyBody = (program: Program, test: Test) =>
  bodies(program).some((body) => holds(body, test));

/** The bodies some `Fork` statement in the program forks, detached or not. */
const forkedBodies = (program: Program, detached: boolean) =>
  bodies(program).flatMap((body) =>
    collect(body, (one) => one._tag === "Fork" && one.detach === detached)
  ).flatMap((one) =>
    one._tag === "Fork" ? [program.forks[one.fiber] ?? []] : []
  );

const bigLoop = (one: Statement) => "count" in one && one.count > 2048;

/** A statement that yields to the executor: a durable step or a yield. */
const yields = (one: Statement) => bigLoop(one) || [
  "Run", "Sleep", "Call", "YieldNow", "RaceDurable", "Timeout",
  "RetrySpaced", "RepeatSpaced",
].includes(one._tag);

const tagged = (tag: Statement["_tag"]) => (one: Statement) =>
  one._tag === tag;

const emitted = (log: ReadonlyArray<LogEntry>, tag: string) =>
  log.some((entry) => entry._tag === "Emitted" && entry.event._tag === tag);

const one = (yes: boolean) => yes ? 1 : 0;

/** The named cases one lifecycle run reached. */
export const shapeScans = (run: LifecycleRun): ShapeScans => {
  const { program, log } = run;
  const detached = forkedBodies(program, true);
  return {
    durableRaces: one(anyBody(program, tagged("RaceDurable"))),
    pureTimeouts: one(anyBody(program, tagged("Timeout"))),
    inlineWakes: run.kinds.inlineWakes,
    blockedChildren: one([...forkedBodies(program, false), ...detached]
      .some((body) => holds(body, tagged("DeferredAwait")))),
    yieldingFinalizers: one(emitted(log, "RootExit") &&
      finalizersIn(program.root).some((body) => holds(body, yields))),
  };
};
