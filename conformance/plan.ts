import type { MutantName } from "./mutants.ts";
import { runProcesses } from "./processes.ts";
import type { Outcome } from "./processes.ts";
import type { Job, Role } from "./runs.ts";

/** The pinned fast-check seeds (dossier, "Runs"). */
export const seeds: ReadonlyArray<number> = [1, 2, 3, 4, 5];

/** Programs per seed (dossier, "Runs"). */
export const programsPerSeed = 1000;

const freshRoles = ["fresh0", "fresh1", "fresh2"] as const;

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
 * The processes for program `index` of every seed: three fresh ones, each
 * running that program once per seed, so that it has run nothing else from
 * a program's seed before the program; and one that runs program
 * `index + 1` of each seed before program `index`.
 */
export const processesFor = (mutant: MutantName | undefined, detail?: Detail) =>
  (index: number): ReadonlyArray<ReadonlyArray<Job>> => {
    const make = job(mutant, detail);
    const next = (index + 1) % programsPerSeed;
    return [
      ...freshRoles.map((role) => seeds.map((seed) => make(seed, index, role))),
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
