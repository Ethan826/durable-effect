import { spawn } from "node:child_process";
import { availableParallelism } from "node:os";
import { fileURLToPath } from "node:url";
import { Option, Schema } from "effect";
import { RunResult } from "./runs.ts";
import type { Job } from "./runs.ts";

const workerPath = fileURLToPath(new URL("./worker.ts", import.meta.url));

/**
 * A worker still running after this long is killed and reported. No job of
 * the suite comes near it: a whole process normally ends within seconds.
 */
const processTimeoutMs = 600_000;

/** Every run reported, and a line for each process that did not end well. */
export interface Outcome {
  readonly results: ReadonlyArray<RunResult>;
  readonly failures: ReadonlyArray<string>;
}

const decodeResult = Schema.decodeUnknownOption(
  Schema.fromJsonString(RunResult),
);

/** What one worker printed, decoded; a line that does not decode fails. */
const outcomeOf = (
  printed: string,
  ending: string | undefined,
): Outcome => {
  const lines = printed.split("\n").filter((line) => line.length > 0);
  const decoded = lines.map((line) => decodeResult(line));
  const results = decoded.flatMap((one) => Option.toArray(one));
  const garbled = decoded.length === results.length ? [] : ["garbled output"];
  return { results, failures: [...garbled, ...Option.toArray(
    Option.fromUndefinedOr(ending),
  )] };
};

const describeJobs = (jobs: ReadonlyArray<Job>) =>
  jobs.map((job) => `${job.seed}/${job.index}/${job.role}`).join(" ");

/** Runs one worker over `jobs`, in a fresh Node process. */
const runWorker = (jobs: ReadonlyArray<Job>) =>
  new Promise<Outcome>((resolve) => {
    const child = spawn(process.execPath, [workerPath]);
    const printed: string[] = [];
    const errors: string[] = [];
    child.stdout.setEncoding("utf8").on("data", (chunk) => printed.push(chunk));
    child.stderr.setEncoding("utf8").on("data", (chunk) => errors.push(chunk));
    const timer = setTimeout(() => child.kill("SIGKILL"), processTimeoutMs);
    child.on("close", (code, signal) => {
      clearTimeout(timer);
      const ending = code === 0 ? undefined : `worker ` +
        `${describeJobs(jobs)} ended ${code ?? signal}: ${errors.join("")}`;
      resolve(outcomeOf(printed.join(""), ending));
    });
    child.stdin.end(JSON.stringify(jobs));
  });

const merge = (outcomes: ReadonlyArray<Outcome>): Outcome => ({
  results: outcomes.flatMap((outcome) => outcome.results),
  failures: outcomes.flatMap((outcome) => outcome.failures),
});

/**
 * Runs each group of jobs in its own fresh worker process, as many at once
 * as the machine has cores, and gathers what they report.
 */
export const runProcesses = async (
  groups: ReadonlyArray<ReadonlyArray<Job>>,
): Promise<Outcome> => {
  const outcomes: Outcome[] = [];
  const cursor = { next: 0 };
  const lane = async (): Promise<void> => {
    const at = cursor.next++;
    const group = groups[at];
    if (group === undefined) return;
    outcomes[at] = await runWorker(group);
    return lane();
  };
  await Promise.all(Array.from({ length: availableParallelism() }, lane));
  return merge(outcomes);
};
