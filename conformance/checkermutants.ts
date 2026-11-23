/**
 * A checker mutant: its name, the checker file it breaks, the text there
 * that is turned off, what replaces it, and the start of the name of a
 * fixture that must then fail.
 */
export type CheckerMutant = readonly [string, string, string, string, string];

const scanFloor = "the scan floor needs the full budget and the required";
const lifecycleScan = "the lifecycle scan needs every program";
const inventory = "an empty inventory, or a kind never generated";
const sequenceId = "the required sequence is the 5,000th";
const sequenceScan = "the sequence scan needs the exact count";
const agree = "the file lists agree with the directory";
const quickList = "the quick list is the full list without determinism";

const comparisons: ReadonlyArray<CheckerMutant> = [
  ["I1 and I2: logs compared", "properties.ts",
    "left.logHash === right.logHash && left.furtherHash === right.furtherHash",
    "true", "I1 catches a differing log"],
  ["I2: the paced run compared", "properties.ts",
    'I2: ["fresh2", "fresh0", "after"]', 'I2: ["fresh0", "after"]',
    "I2 catches a paced run whose log differs"],
  ["I7: a repeated id", "properties.ts",
    "new Set(run.identities).size !== run.identities.length", "false",
    "I7 catches a repeated id"],
  ["I7: ids between runs", "properties.ts",
    "JSON.stringify(left.identities) === JSON.stringify(right.identities)",
    "true", "I7 catches a repeated id"],
  ["I9: the limits", "properties.ts", "run[measure] > limit", "false",
    "I9 allows maxLoop at 2049"],
  ["a missing run", "properties.ts", 'cause: "run", roles: missing',
    'cause: "property", roles: missing',
    "a run missing from a program is a run finding"],
];

const determinismScan: ReadonlyArray<CheckerMutant> = [
  ["programs compared", "properties.ts", "compared[property].every(",
    "compared[property].some(",
    "programs compared counts the programs with every run needed"],
  ["the required program", "plan.ts", "run.index === requiredProgram.index",
    "true", scanFloor],
  ["the required program's seed", "plan.ts",
    "run.seed === requiredProgram.seed &&", "true &&", scanFloor],
];

const lifecycleScans: ReadonlyArray<CheckerMutant> = [
  ["the lifecycle required program", "lifeplan.ts",
    "\n  outcome.reachedRequired;", "\n  true;", lifecycleScan],
  ["the lifecycle program count", "lifeplan.ts",
    "outcome.programs >= seeds.length * programsPerSeed &&", "true &&",
    lifecycleScan],
  ["the lifecycle required program's index", "lifeplan.ts",
    "place.index === requiredProgram.index", "true",
    "a lifecycle run reaches the required program"],
];

const inventoryAndSequences: ReadonlyArray<CheckerMutant> = [
  ["an empty inventory", "inventory.ts", "required.length === 0", "false",
    inventory],
  ["a missing kind", "inventory.ts", "!seen.has(kind)", "false", inventory],
  ["the required sequence's seed", "strays.ts",
    "seed === requiredSequence.seed &&", "true &&", sequenceId],
  ["the required sequence's number", "strays.ts",
    "number === requiredSequence.number", "true", sequenceId],
  ["the sequence count", "strays.ts", "runs === budget &&", "true &&",
    sequenceScan],
  ["the required sequence", "strays.ts", "runs === budget && reachedRequired",
    "runs === budget && true", sequenceScan],
];

const listings: ReadonlyArray<CheckerMutant> = [
  ["a file no script runs", "listing.ts", "onDisk.filter((file) => !full.in",
    "onDisk.filter((file) => false && !full.in", agree],
  ["a listed file not on disk", "listing.ts",
    "full.filter((file) => !onDisk.includes(file))",
    "full.filter(() => false)", agree],
  ["a file missing from quick", "listing.ts",
    "file !== leftOutOfQuick && !quick.includes(file)", "false", quickList],
  ["a stray file in quick", "listing.ts",
    "file === leftOutOfQuick || !full.includes(file)", "false", quickList],
  ["the minimum file count", "listing.ts", "onDisk.length < minimum", "false",
    "a directory below the minimum file count"],
];

/** Every checker mutant of the gate: gate.check.ts runs each in turn. */
export const mutants: ReadonlyArray<CheckerMutant> = [
  ...comparisons, ...determinismScan, ...lifecycleScans,
  ...inventoryAndSequences, ...listings,
];
