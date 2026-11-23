import type { MutantName } from "./mutants.ts";
import { runProcesses } from "./processes.ts";
import type { Outcome } from "./processes.ts";
import type { Job, Role } from "./runs.ts";

/** The pinned fast-check seeds (dossier, "Runs"). */
export const seeds: ReadonlyArray<number> = [1, 2, 3, 4, 5];

/** Programs per seed (dossier, "Runs"). */
export const programsPerSeed = 1000;

const freshRoles = ["fresh0", "fresh1", "fresh2"] as const;

/** Runs reported for the full budget: four roles, every seed and program. */
const fullBudgetRuns = (freshRoles.length + 1) * seeds.length * programsPerSeed;

/**
 * The program every full scan must reach: the last of the last seed. A
 * scan that stops early, or skips a seed, does not contain it.
 */
export const requiredProgram = { seed: 5, index: 999 } as const;

/** The scan minimum: every run of the full budget, the required program's. */
export const fullScan = (outcome: Outcome): boolean =>
  outcome.results.length >= fullBudgetRuns &&
  outcome.results.filter((run) =>
    run.seed === requiredProgram.seed && run.index === requiredProgram.index
  ).length >= freshRoles.length + 1;

/** Which runs report their whole log: none, or one seed's. */
type Detail = { readonly seed: number } | undefined;

/**
 * One run of program `index` of `seed`. Only `fresh2` is paced, so that
 * timers and callbacks can fire between its tasks; the I1 runs are not.
 */
const job = (mutant: MutantName | undefined, detail: Detail) =>
  (seed: number, index: number, role: Role): Job => ({
    seed, index, role, mutant,
    detail: detail?.seed === seed,
    pacing: role === "fresh2" ? "timer" : "none",
  });

/**
 * The processes for program `index` of every seed. Each fresh run gets a
 * process of its own, which runs nothing else: three per seed. The last
 * process runs program `index + 1` of each seed before program `index`, so
 * each `after` run follows another program of the same seed.
 */
export const processesFor = (mutant: MutantName | undefined, detail?: Detail) =>
  (index: number): ReadonlyArray<ReadonlyArray<Job>> => {
    const make = job(mutant, detail);
    const next = (index + 1) % programsPerSeed;
    return [
      ...freshRoles.flatMap((role) =>
        seeds.map((seed) => [make(seed, index, role)])
      ),
      seeds.flatMap((seed) => [
        make(seed, next, "warmup"),
        make(seed, index, "after"),
      ]),
    ];
  };

const indices = (from: number, to: number) =>
  Array.from({ length: to - from }, (_, offset) => from + offset);

/** Every run of programs `from` to `to - 1` of every seed. */
export const runRange = (
  mutant: MutantName | undefined,
  from: number,
  to: number,
): Promise<Outcome> =>
  runProcesses(indices(from, to).flatMap(processesFor(mutant)));
