// A conformance worker: run by `processes.ts` as `node conformance/worker.ts`
// with a JSON array of jobs on stdin. It runs the jobs in order, in this one
// process, and prints one JSON line per reported job to stdout. A `warmup`
// job runs but is not reported. Exit code 1 when the input does not decode
// or a job names no program.
import { text } from "node:stream/consumers";
import { Option, Schema } from "effect";
import { Job, runJob } from "./runs.ts";
import type { RunResult } from "./runs.ts";

const decodeJobs = Schema.decodeUnknownOption(
  Schema.fromJsonString(Schema.Array(Job)),
);

const fail = (message: string) => {
  process.stderr.write(`${message}\n`);
  process.exitCode = 1;
};

const report = (job: Job) => (result: Option.Option<RunResult>) =>
  Option.match(result, {
    onNone: () => fail(`no program for seed ${job.seed} index ${job.index}`),
    onSome: (run) => {
      if (job.role !== "warmup") {
        process.stdout.write(`${JSON.stringify(run)}\n`);
      }
    },
  });

/** Runs the jobs one after another, each after the last has finished. */
const runAll = (jobs: ReadonlyArray<Job>) =>
  jobs.reduce(
    (previous: Promise<void>, job) =>
      previous.then(() => runJob(job)).then(report(job)),
    Promise.resolve(),
  );

const input = await text(process.stdin);
await Option.match(decodeJobs(input), {
  onNone: () => Promise.resolve(fail("the jobs on stdin did not decode")),
  onSome: runAll,
});
