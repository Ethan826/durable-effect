import { Option } from "effect";
import type { Journal } from "./deliveries.ts";
import { foreignRuns } from "./foreign.ts";
import type { ForeignRun, Placement, Target } from "./foreign.ts";
import type { Program } from "./grammar.ts";
import { i3Breach } from "./i3check.ts";
import { lifecycleChecks, scansOf } from "./lifecheck.ts";
import type { Scans } from "./lifecheck.ts";
import { shapeScans } from "./shapes.ts";
import type { ShapeScans } from "./shapes.ts";
import { lifecycleRun } from "./lifecycle.ts";
import type { LifecycleProperty, Variant } from "./mutants.ts";
import { programsPerSeed, requiredProgram, seeds } from "./plan.ts";
import type { Violation } from "./properties.ts";
import { caseAt } from "./runs.ts";

/** The lifecycle properties, in the order #37's table lists them. */
export const lifecycleProperties: ReadonlyArray<LifecycleProperty> = [
  "I3", "I4", "I5", "I6", "I8",
];

/** Every count the lifecycle runs keep: I3's and the lifecycle run's. */
export interface AllScans extends Scans, ShapeScans {
  readonly foreignResumes: number;
  readonly foreignInterrupts: number;
  readonly maskedWaiters: number;
}

/** No count yet. */
export const zeroScans: AllScans = {
  unmaskedInterrupts: 0, maskedInterrupts: 0, lateDeliveries: 0,
  cancels: 0, idleTasks: 0, successExits: 0, failureExits: 0,
  interruptedExits: 0, fibers: 0, internalFibers: 0, detachedFibers: 0,
  closingRegistrations: 0, durableRaces: 0, pureTimeouts: 0, inlineWakes: 0,
  blockedChildren: 0, yieldingFinalizers: 0, maskedClosingRegistrations: 0,
  foreignResumes: 0, foreignInterrupts: 0, maskedWaiters: 0,
};

/** The programs run, each property's first violation, and the counts. */
export interface LifeOutcome {
  readonly programs: number;
  readonly violations: Partial<Record<LifecycleProperty, Violation>>;
  readonly scans: AllScans;
  /** Whether the run of `requiredProgram` finished. */
  readonly reachedRequired: boolean;
}

type Floor = readonly [keyof AllScans, number];

/**
 * The scan minimums: what each property's check must have examined over
 * the full budget, and the cases of #37's "Conformance test" column the
 * grammar reaches (shapes.ts). Each is the count the adapter's full
 * budget gave when it was set (Task 12), rounded down to two significant
 * figures, so a check that stops looking, or a grammar that stops
 * reaching a case, fails here. Measured: foreign resumes 3,775 (in the
 * first resuming run), foreign interrupts 520,241 (in the interrupt-only
 * run), masked waiters resumed 1,898; interrupts of awaits 2,034
 * unmasked and 30,094 masked, late deliveries 2,384, cancels 144,
 * programs with a durable race 1,384 and with a pure timeout 1,383; idle
 * tasks 112,666, inline forks 4,530, inline wakes 550, forked bodies
 * awaiting a deferred 100; root exits 1,294 success, 193 failure, 2,035
 * interrupted, past a finalizer that may yield 316; fibers 10,100,
 * detached 153, registered while closing 66. I8's case of a fiber masked
 * when it registers during closing measures 0 here and has no floor: the
 * grammar cannot start a fork masked (grammar.ts:59), so closing.ts pins
 * it.
 */
export const scanMinimums: Readonly<Record<LifecycleProperty, ReadonlyArray<
  Floor
>>> = {
  I3: [
    ["foreignResumes", 3700], ["foreignInterrupts", 520_000],
    ["maskedWaiters", 1800],
  ],
  I4: [
    ["unmaskedInterrupts", 2000], ["maskedInterrupts", 30_000],
    ["lateDeliveries", 2300], ["cancels", 140], ["durableRaces", 1300],
    ["pureTimeouts", 1300],
  ],
  I5: [
    ["idleTasks", 110_000], ["internalFibers", 4500], ["inlineWakes", 550],
    ["blockedChildren", 100],
  ],
  I6: [
    ["successExits", 1200], ["failureExits", 190],
    ["interruptedExits", 2000], ["yieldingFinalizers", 310],
  ],
  I8: [
    ["fibers", 10_000], ["internalFibers", 4500], ["detachedFibers", 150],
    ["closingRegistrations", 66],
  ],
};

/** Each of the property's counts below its minimum, described. */
export const shortfall = (
  property: LifecycleProperty,
  outcome: LifeOutcome,
): ReadonlyArray<string> =>
  scanMinimums[property].flatMap(([name, floor]) =>
    outcome.scans[name] < floor ? [`${name} ${outcome.scans[name]} < ${floor}`]
      : []
  );

/** The scan minimum on programs: every program of the full budget ran. */
export const fullScanOf = (outcome: LifeOutcome): boolean =>
  outcome.programs >= seeds.length * programsPerSeed &&
  outcome.reachedRequired;

const targets: ReadonlyArray<Target> = ["root", "child", "detached"];

/** I3's placement for program `index`: each target, masked and not. */
const placementOf = (index: number): Placement => ({
  target: targets[index % targets.length] ?? "root",
  masked: Math.floor(index / targets.length) % 2 === 1,
});

/** The state of one budget's run, as it goes. */
interface Tally {
  programs: number;
  readonly violations: Partial<Record<LifecycleProperty, Violation>>;
  scans: AllScans;
  reachedRequired: boolean;
}

const scanNames = Object.keys(zeroScans).filter(
  (name): name is keyof AllScans => name in zeroScans,
);

/** The counts with `more` added. */
const add = (scans: AllScans, more: Partial<AllScans>): AllScans => {
  const sum: { -readonly [K in keyof AllScans]: number } = { ...scans };
  scanNames.forEach((name) => {
    sum[name] = scans[name] + (more[name] ?? 0);
  });
  return sum;
};

/** Where a finding was made. */
interface Place {
  readonly seed: number;
  readonly index: number;
}

/** Keeps the first violation of each property. */
const note = (tally: Tally, place: Place, cause: Violation["cause"]) =>
  (property: LifecycleProperty, detail: string | undefined) => {
    if (detail === undefined || tally.violations[property]) return;
    tally.violations[property] =
      { property, cause, ...place, roles: [], detail };
  };

const i3Scans = (runs: ReadonlyArray<ForeignRun>, placement: Placement) => ({
  foreignResumes: runs[2]?.sent.resumes ?? 0,
  foreignInterrupts: runs[1]?.sent.interrupts ?? 0,
  maskedWaiters: placement.masked && (runs[2]?.sent.resumes ?? 0) > 0 ? 1 : 0,
});

type Checked = Exclude<LifecycleProperty, "I3">;
const isChecked = (property: LifecycleProperty): property is Checked =>
  property !== "I3";

/** What one program's runs need: the case, where it is, the variant. */
interface Job {
  readonly sampled: readonly [Program, Journal];
  readonly place: Place;
  readonly make: Variant;
}

/** I3's three runs of one program. */
const runI3 = async ({ sampled, place, make }: Job, tally: Tally) => {
  const placement = placementOf(place.index);
  const runs = await foreignRuns(sampled, place.index, placement, make);
  note(tally, place, "property")("I3", i3Breach(runs));
  tally.scans = add(tally.scans, i3Scans(runs, placement));
};

/** One lifecycle run, checked for each of `checked`. */
const runChecked = async (
  { sampled, place, make }: Job,
  checked: ReadonlyArray<Checked>,
  tally: Tally,
) => {
  const run = await lifecycleRun(sampled, place.index, make);
  const found = note(tally, place, "property");
  checked.forEach((property) =>
    found(property, lifecycleChecks[property](run))
  );
  tally.scans = add(add(tally.scans, scansOf(run)), shapeScans(run));
};

/** Runs one program for `properties` and adds what it finds. */
const runProgram = async (
  job: Job,
  properties: ReadonlyArray<LifecycleProperty>,
  tally: Tally,
) => {
  if (properties.includes("I3")) await runI3(job, tally);
  const checked = properties.filter(isChecked);
  if (checked.length > 0) await runChecked(job, checked, tally);
};

/** One program, with a thrown error or a missing program a run finding. */
const runPlace = async (
  place: Place,
  make: Variant,
  properties: ReadonlyArray<LifecycleProperty>,
  tally: Tally,
) => {
  const failed = (detail: string) => properties.forEach((property) =>
    note(tally, place, "run")(property, detail)
  );
  const sampled = caseAt(place.seed, place.index);
  if (Option.isNone(sampled)) return failed("no program");
  try {
    await runProgram({ sampled: sampled.value, place, make }, properties,
      tally);
    tally.programs += 1;
    tally.reachedRequired ||= place.seed === requiredProgram.seed &&
      place.index === requiredProgram.index;
  } catch (error) {
    failed(`the run threw: ${String(error)}`);
  }
};

/**
 * Runs programs `from` to `to - 1` of every seed, in program order, under
 * `make`, for the given properties, in this process.
 */
export const runLifecycle = async (
  make: Variant,
  from: number,
  to: number,
  properties: ReadonlyArray<LifecycleProperty> = lifecycleProperties,
): Promise<LifeOutcome> => {
  const tally: Tally = {
    programs: 0, violations: {}, scans: zeroScans, reachedRequired: false,
  };
  const places = Array.from({ length: to - from }, (_, at) => from + at)
    .flatMap((index) => seeds.map((seed) => ({ seed, index })));
  await places.reduce(
    (previous: Promise<void>, place) =>
      previous.then(() => runPlace(place, make, properties, tally)),
    Promise.resolve(),
  );
  return tally;
};
