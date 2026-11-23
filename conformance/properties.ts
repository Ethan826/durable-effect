import type { Property } from "./mutants.ts";
import type { Outcome } from "./processes.ts";
import { maxStatementLoops } from "./runloops.ts";
import type { Role, RunResult } from "./runs.ts";

/** The properties this suite checks, in the order #37's table lists them. */
export const properties: ReadonlyArray<Property> = ["I1", "I2", "I7", "I9"];

/**
 * I9's main check: no run loop passes B + 1 = 2,049 operations, B being
 * `MaxOpsBeforeYield`. An operation is one increment of `currentOpCount`;
 * `succeedWith` returns at multiples of 32 (internal/effect.ts:765, :843)
 * and 2,048 is one, so a loop checks the scheduler by its 2,049th.
 */
export const maxOpsPerLoop = 2049;

/**
 * I9's per-task ceiling, (B + d)(S·W + K·L) + 2·W·K·L·t with B 2,048,
 * d 32, S 24, W 8, K 4, L 384 and t 8 (dossier, "Runs").
 */
export const maxOpsPerTask = 3_790_848;

/**
 * A property that failed: on which program, and how. `cause` is
 * `property` when the runs' contents break it, and `run` when a run is
 * missing or a worker crashed, timed out or printed what does not decode,
 * which says nothing about the property.
 */
export interface Violation {
  readonly property: Property;
  readonly cause: "property" | "run";
  readonly seed: number;
  readonly index: number;
  readonly roles: ReadonlyArray<Role>;
  readonly detail: string;
}

type Runs = Partial<Record<Role, RunResult>>;

/** The runs each property compares; I7 and I9 look at every run. */
const compared: Readonly<Record<Property, ReadonlyArray<Role>>> = {
  I1: ["fresh0", "fresh1", "after"],
  I2: ["fresh2", "fresh0", "after"],
  I7: ["fresh0", "fresh1", "fresh2", "after"],
  I9: ["fresh0", "fresh1", "fresh2", "after"],
};

const sameRun = (left: RunResult, right: RunResult) =>
  left.logHash === right.logHash && left.furtherHash === right.furtherHash;

const sameIdentities = (left: RunResult, right: RunResult) =>
  JSON.stringify(left.identities) === JSON.stringify(right.identities);

const repeated = (run: RunResult) =>
  new Set(run.identities).size !== run.identities.length;

type Finding = Pick<Violation, "roles" | "detail"> | undefined;
type Found = Pick<Violation, "cause" | "roles" | "detail"> | undefined;

/**
 * I1 and I2: each run's log and further tasks match the first run's (for
 * I2, the paced `fresh2`).
 */
const logsMatch = (runs: ReadonlyArray<RunResult>): Finding => {
  const [first, ...rest] = runs;
  const other = rest.find((run) => first !== undefined && !sameRun(first, run));
  if (first === undefined || other === undefined) return undefined;
  const part = first.logHash === other.logHash ? "further tasks" : "log";
  return { roles: [first.role, other.role], detail: `${part} differs` };
};

/** I7: no identity registered twice in a run, the same in every run. */
const identitiesHold = (runs: ReadonlyArray<RunResult>): Finding => {
  const twice = runs.find(repeated);
  if (twice !== undefined) {
    const ids = twice.identities.join(",");
    return { roles: [twice.role], detail: `an id is reused: ${ids}` };
  }
  const [first, ...rest] = runs;
  const other = rest.find((run) =>
    first !== undefined && !sameIdentities(first, run)
  );
  if (first === undefined || other === undefined) return undefined;
  const shown = `${first.identities.join(",")} / ${other.identities.join(",")}`;
  return { roles: [first.role, other.role], detail: `ids differ: ${shown}` };
};

type Measure = "maxLoop" | "framed" | "statementLoops" | "maxOps";

/** I9's limits, in the order they are checked, with what each counts. */
const limits: ReadonlyArray<readonly [Measure, number, string]> = [
  ["maxLoop", maxOpsPerLoop, "operations in one run loop"],
  ["framed", 0, "fibers first met the scheduler with frames"],
  ["statementLoops", maxStatementLoops, "statement-fiber loops in a task"],
  ["maxOps", maxOpsPerTask, "operations in one task"],
];

/** I9: every run within each limit, the per-run-loop bound first. */
const tasksBounded = (runs: ReadonlyArray<RunResult>): Finding => {
  const breaches = limits.flatMap(([measure, limit, what]) =>
    runs.filter((run) => run[measure] > limit).map((run) => ({
      roles: [run.role],
      detail: `${run[measure]} > ${limit} ${what}`,
    }))
  );
  return breaches[0];
};

const checks: Readonly<Record<Property, typeof logsMatch>> = {
  I1: logsMatch,
  I2: logsMatch,
  I7: identitiesHold,
  I9: tasksBounded,
};

/** Groups runs by program: `seed/index` to the runs by role. */
const byProgram = (results: ReadonlyArray<RunResult>) =>
  results.reduce((groups, run) => {
    const key = `${run.seed}/${run.index}`;
    groups.set(key, { ...groups.get(key), [run.role]: run });
    return groups;
  }, new Map<string, Runs>());

/** A missing run, else what the property's check finds in the runs. */
const findingIn = (
  property: Property,
  runs: Runs,
  present: ReadonlyArray<RunResult>,
): Found => {
  const missing = compared[property].filter((role) => runs[role] === undefined);
  if (missing.length > 0) {
    return { cause: "run", roles: missing, detail: "run missing" };
  }
  const finding = checks[property](present);
  return finding && { cause: "property", ...finding };
};

/** The first violation of one program's runs, a missing run included. */
const violationIn = (property: Property) =>
  (runs: Runs): Violation | undefined => {
    const present = compared[property].flatMap((role) => runs[role] ?? []);
    const [first] = present;
    if (first === undefined) return undefined;
    const found = findingIn(property, runs, present);
    const { seed, index } = first;
    return found && { property, seed, index, ...found };
  };

/**
 * The first violation of `property` in an outcome, in program order. A
 * process that crashed or timed out is a violation of every property.
 */
export const check = (
  property: Property,
  outcome: Outcome,
): Violation | undefined => {
  const [failure] = outcome.failures;
  if (failure !== undefined) {
    const where = { seed: 0, index: 0, roles: [] };
    return { property, cause: "run", ...where, detail: failure };
  }
  const groups = [...byProgram(outcome.results).values()];
  return groups.map(violationIn(property)).find((found) => found);
};

/** One line for a test's output; empty for no violation. */
export const describe = (violation: Violation | undefined): string =>
  violation === undefined ? "" : [
    `${violation.property} fails on seed ${violation.seed}`,
    `program ${violation.index}`,
    `runs ${violation.roles.join(", ")}: ${violation.detail}`,
  ].join(", ");
