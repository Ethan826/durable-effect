import { createHash } from "node:crypto";
import { setImmediate, setTimeout } from "node:timers/promises";
import { Option, Schema } from "effect";
import fc from "fast-check";
import type {
  AdapterRuntime,
  FiberId,
  Task,
} from "../src/adapter/Interface.ts";
import { makeAdapter } from "../src/adapter/Runtime.ts";
import { journal, program } from "./grammar.ts";
import type { Journal } from "./deliveries.ts";
import type { Program } from "./grammar.ts";
import { scriptedHost } from "./host.ts";
import type { LogEntry, Pause, ScriptedHost } from "./host.ts";
import { interpret } from "./interpret.ts";
import { further } from "./further.ts";
import {
  checkedRegistration,
  counted,
  freshCount,
  perTask,
} from "./opcount.ts";
import { beginTask, endTask } from "./runloops.ts";
import { mutantNames, mutants } from "./mutants.ts";

const roles = ["fresh0", "fresh1", "fresh2", "after", "warmup"] as const;

/**
 * Which run of a program a job is: one of three in fresh processes, the
 * one after another program, or that other program (`warmup`, unreported).
 */
export type Role = typeof roles[number];

/** One program run for a worker: by seed and index, with its pacing. */
export const Job = Schema.Struct({
  seed: Schema.Int,
  index: Schema.Int,
  role: Schema.Literals(roles),
  pacing: Schema.Literals(["none", "timer"]),
  mutant: Schema.optionalKey(Schema.Literals(mutantNames)),
  detail: Schema.Boolean,
});
/** One program run for a worker: by seed and index, with its pacing. */
export type Job = typeof Job.Type;

/**
 * What a worker reports of a run. The hashes cover the log without its
 * `Global` entries (report-only, #37 I2), and the log of the three
 * further tasks; `identities` lists each `register` question's fiber in
 * order. For I9: `maxOps` is the most operations any one task ran,
 * `maxLoop` the most in one run loop, `misregistered` the fibers registered
 * after their first operation or with frames (opcount.ts), and
 * `statementLoops` the most statement-fiber run loops in one task
 * (runloops.ts). `log` is the whole visible log, one JSON string per
 * entry, when the job asked for it.
 */
export const RunResult = Schema.Struct({
  seed: Schema.Int,
  index: Schema.Int,
  role: Schema.Literals(roles),
  logHash: Schema.String,
  furtherHash: Schema.String,
  identities: Schema.Array(Schema.Int),
  maxOps: Schema.Int,
  maxLoop: Schema.Int,
  misregistered: Schema.Int,
  statementLoops: Schema.Int,
  log: Schema.optionalKey(Schema.Array(Schema.String)),
});
/** What a worker reports of a run. */
export type RunResult = typeof RunResult.Type;

const cases = fc.tuple(program, journal);

/** Program `index` of `seed`: the same as `fc.sample` at that index. */
export const caseAt = (
  seed: number,
  index: number,
): Option.Option<readonly [Program, Journal]> =>
  Option.fromUndefinedOr(
    fc.sample(cases, { seed, numRuns: 1, path: String(index) })[0],
  );

const isPowerOfTwo = (steps: number) => (steps & (steps - 1)) === 0;

/**
 * The perturbed pacing: a 1 ms timer after steps 1, 2, 4, 8 and so on, so
 * that timers can fire, and a macrotask turn after every other step.
 */
const timerPause: Pause = async (steps) => {
  await (isPowerOfTwo(steps) ? setTimeout(1) : setImmediate());
};

const visible = (entry: LogEntry) => entry._tag !== "Global";
const hashOf = (entries: ReadonlyArray<LogEntry>) =>
  createHash("sha256").update(JSON.stringify(entries)).digest("hex");

const identitiesIn = (log: ReadonlyArray<LogEntry>): FiberId[] =>
  log.flatMap((entry) =>
    entry._tag === "Answered" && entry.question === "register"
      ? [entry.fiber]
      : []
  );

/** I9's measures of one run. */
type Measures = Pick<
  RunResult,
  "maxOps" | "maxLoop" | "misregistered" | "statementLoops"
>;

/** The runtime, with the statement-loop oracle read after each task. */
const loopsPerTask = (
  runtime: AdapterRuntime,
  most: { statementLoops: number },
): AdapterRuntime => ({
  runTask: (task) => {
    beginTask();
    runtime.runTask(task);
    most.statementLoops = Math.max(most.statementLoops, endTask());
  },
});

/** The result of a run whose log ends with the further tasks' entries. */
const summarize = (
  job: Job,
  log: ReadonlyArray<LogEntry>,
  mainLength: number,
  measures: Measures,
): RunResult => ({
  seed: job.seed,
  index: job.index,
  role: job.role,
  logHash: hashOf(log.slice(0, mainLength).filter(visible)),
  furtherHash: hashOf(log.slice(mainLength).filter(visible)),
  identities: identitiesIn(log),
  ...measures,
  log: job.detail
    ? log.filter(visible).map((entry) => JSON.stringify(entry))
    : undefined,
});

/**
 * The adapter, or the job's mutant, for `shape` under `host`, with I9's
 * counters around it, and a reader of what they measured.
 */
const instrumented = (job: Job, shape: Program, host: ScriptedHost) => {
  const count = freshCount();
  const most = { statementLoops: 0 };
  const make = job.mutant === undefined ? makeAdapter
    : mutants[job.mutant].make;
  const adapter = loopsPerTask(perTask(
    make(counted(interpret(shape), count), 0,
      checkedRegistration(host, count)), count), most);
  const measures = (): Measures => ({
    maxOps: count.max,
    maxLoop: count.maxLoop,
    misregistered: count.misregistered,
    statementLoops: most.statementLoops,
  });
  return { adapter, measures };
};

/**
 * Runs one job in this process: the program under the adapter or the named
 * mutant, paced or not, then the three further tasks from its final state.
 */
export const runCase = async (job: Job, [shape, script]: readonly [
  Program,
  Journal,
]): Promise<RunResult> => {
  const host = scriptedHost(script, { seed: job.index });
  const { adapter, measures } = instrumented(job, shape, host);
  if (job.pacing === "timer") await host.runPaced(adapter, timerPause);
  else host.run(adapter);
  const mainLength = host.log.length;
  further(host.log).forEach((task: Task) => host.extend(adapter, task));
  return summarize(job, host.log, mainLength, measures());
};

/** Runs one job; none when its seed and index give no program. */
export const runJob = (job: Job): Promise<Option.Option<RunResult>> =>
  Option.match(caseAt(job.seed, job.index), {
    onNone: () => Promise.resolve(Option.none()),
    onSome: (sampled) => runCase(job, sampled).then(Option.some),
  });
