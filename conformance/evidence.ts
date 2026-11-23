import { Option } from "effect";
import type { MutantName } from "./mutants.ts";
import { processesFor } from "./plan.ts";
import { runProcesses } from "./processes.ts";
import { describe } from "./properties.ts";
import type { Violation } from "./properties.ts";
import { caseAt } from "./runs.ts";
import type { RunResult } from "./runs.ts";

const shown = (entry: string | undefined) => entry ?? "(log ended)";

/** Where two logs first part, with the entry each holds there. */
const firstDifference = (
  left: ReadonlyArray<string>,
  right: ReadonlyArray<string>,
): string => {
  const length = Math.max(left.length, right.length);
  const at = Array.from({ length }, (_, offset) => offset)
    .find((offset) => left[offset] !== right[offset]);
  if (at === undefined) return "the rerun's logs agree";
  return `entry ${at}: ${shown(left[at])} / ${shown(right[at])}`;
};

/** The whole log of one seed's run in a role; empty when not reported. */
const logOf = (results: ReadonlyArray<RunResult>, seed: number) =>
  (role: string): ReadonlyArray<string> =>
    results.find((run) => run.seed === seed && run.role === role)?.log ?? [];

/**
 * Reruns the violation's program in the same processes, with whole logs
 * for its seed, and gives where the two runs it names first part.
 */
const rerunDifference = async (
  violation: Violation,
  mutant: MutantName,
): Promise<string> => {
  const { seed, index, roles } = violation;
  const outcome = await runProcesses(processesFor(mutant, { seed })(index));
  const [left = [], right = []] = roles.map(logOf(outcome.results, seed));
  return firstDifference(left, right);
};

const programOf = (violation: Violation) =>
  Option.match(caseAt(violation.seed, violation.index), {
    onNone: () => "(no program)",
    onSome: (sampled) => JSON.stringify(sampled),
  });

/**
 * A mutant's failing run, for the test's output: the violation, the
 * program and journal, and, when two runs' logs differ, where.
 */
export const evidence = async (
  violation: Violation,
  mutant: MutantName,
): Promise<string> => {
  const compares = violation.roles.length === 2 &&
    violation.detail.endsWith("differs");
  const where = compares ? await rerunDifference(violation, mutant) : "";
  return [describe(violation), where, `case ${programOf(violation)}`]
    .filter((line) => line.length > 0)
    .join("\n");
};
