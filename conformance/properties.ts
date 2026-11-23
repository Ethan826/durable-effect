import type { Property } from "./mutants.ts";
import type { Outcome } from "./processes.ts";
import type { Role, RunResult } from "./runs.ts";

/** The properties this suite checks, in the order #37's table lists them. */
export const properties: ReadonlyArray<Property> = ["I1", "I2", "I7", "I9"];

/**
 * I9's bound on one task: `MaxOpsBeforeYield` times the widest immediate
 * fork plus one, a concurrent `forEach` of 8 elements (dossier, "Runs").
 */
export const maxOpsPerTask = 2048 * 9;

/** A property that failed: on which program, and how. */
export interface Violation {
  readonly property: Property;
  readonly seed: number;
  readonly index: number;
  readonly roles: ReadonlyArray<Role>;
  readonly detail: string;
}

type Runs = Partial<Record<Role, RunResult>>;

/** The runs each property compares; I7 and I9 look at every run. */
const compared: Readonly<Record<Property, ReadonlyArray<Role>>> = {
  I1: ["fresh0", "fresh1", "after"],
  I2: ["fresh0", "fresh2"],
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

/** I1 and I2: each run's log and further tasks match the first run's. */
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

/** I9: every task of every run within the bound. */
const tasksBounded = (runs: ReadonlyArray<RunResult>): Finding => {
  const over = runs.find((run) => run.maxOps > maxOpsPerTask);
  if (over === undefined) return undefined;
  const detail = `a task ran ${over.maxOps} > ${maxOpsPerTask} operations`;
  return { roles: [over.role], detail };
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

/** The first violation of one program's runs, a missing run included. */
const violationIn = (property: Property) =>
  (runs: Runs): Violation | undefined => {
    const wanted = compared[property];
    const present = wanted.flatMap((role) => runs[role] ?? []);
    const [first] = present;
    if (first === undefined) return undefined;
    const missing = wanted.filter((role) => runs[role] === undefined);
    const found: Finding = missing.length > 0
      ? { roles: missing, detail: "run missing" }
      : checks[property](present);
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
    return { property, seed: 0, index: 0, roles: [], detail: failure };
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
