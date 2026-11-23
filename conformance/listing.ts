/** The file the quick run leaves out: it takes most of the full run. */
export const leftOutOfQuick = "determinism.check.ts";

/**
 * Where the scripts' file lists and the directory disagree: a check file
 * no script runs, an entry for a file that is not there, a quick list that
 * is not the full list without `leftOutOfQuick`, or fewer files than
 * `minimum` (the directory has lost files, or the scan read none).
 */
export const listingGaps = (
  onDisk: ReadonlyArray<string>,
  full: ReadonlyArray<string>,
  quick: ReadonlyArray<string>,
  minimum: number,
): ReadonlyArray<string> => [
  ...onDisk.filter((file) => !full.includes(file))
    .map((file) => `${file} is run by no script`),
  ...full.filter((file) => !onDisk.includes(file))
    .map((file) => `${file} is listed but not on disk`),
  ...full.filter((file) => file !== leftOutOfQuick && !quick.includes(file))
    .map((file) => `${file} is missing from the quick list`),
  ...quick.filter((file) => file === leftOutOfQuick || !full.includes(file))
    .map((file) => `${file} should not be in the quick list`),
  ...(onDisk.length < minimum ? [`only ${onDisk.length} files`] : []),
];
