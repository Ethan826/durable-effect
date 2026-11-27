// tick.check.mjs: checks by verdicts the reduction that tier.mjs explores
// some programs with no ticks: those ticks.mjs's dropsTicks accepts, with
// no run and not both a sleep and a clock read. For every such program
// within the bounds, under the base model and every mutant, it explores
// the program with merged.mjs with ticks and without, and requires the
// sets of failing statement ids to be equal. Readings follow tier.mjs:
// {0} for every program, and also {0, 2, 3} for a program with a sleep or
// a clock read. A run is one (program, model, readings); a run where
// either side passes the node cap is counted and not compared.
//
//   node tick.check.mjs <fibers> <statements> <ops> [workers] [cap]
//     the base model and every MUTANTS key; exits 0 only if no run
//     differs and no run passes the cap.
//   node tick.check.mjs control <fibers> <statements> <ops> [workers] [cap]
//     every CONTROL_MUTANTS key: hostTimeLink, which shortens a sleep
//     link by the host clock; exits 0 only if some run differs, which
//     shows the check can fail. Run it at 1 fiber, 2 statements, 1
//     operation: a sleep and its await are enough.
//
// Workers take the selected programs round-robin by their position among
// the selected programs, so the shares stay even. The output names a
// program by its generator index (counting every program, as tier.mjs
// does). Results are sorted by that index before printing, so stdout
// depends on neither scheduling nor the worker count. Progress goes to
// stderr.
import {
  Worker, isMainThread, parentPort, workerData,
} from "node:worker_threads";
import { availableParallelism } from "node:os";
import * as model from "./model.mjs";
import { explore } from "./merged.mjs";
import { dropsTicks, kinds } from "./ticks.mjs";

// The readings sets tier.mjs explores the program with, across its tiers.
const readingsFor = (has) =>
  has.has("sleep") || has.has("clock") ? [[0], [0, 2, 3]] : [[0]];

const modelsFor = (control) => control
  ? Object.keys(model.CONTROL_MUTANTS)
  : [null, ...Object.keys(model.MUTANTS)];

const failing = (result) => [...result.failures.keys()].sort();
const sameSet = (a, b) => a.join(",") === b.join(",");

// One run: the program under one model and readings, with and without
// ticks. Returns null when either side passes the cap.
const compareRun = (program, mutant, readings, cap) => {
  const ticked = explore(program, { mutant, limits: { readings } }, cap);
  if (ticked.capped) return null;
  const limits = { readings, ticks: 0 };
  const plain = explore(program, { mutant, limits }, cap);
  if (plain.capped) return null;
  return { leavesChanged: ticked.leaves !== plain.leaves,
    withTicks: failing(ticked), without: failing(plain) };
};

const recordRun = (out, run, where) => {
  if (run === null) {
    out.capped.push(where);
    return;
  }
  if (run.leavesChanged) out.leavesChanged += 1;
  if (sameSet(run.withTicks, run.without)) return;
  out.diffs.push({ ...where, withTicks: run.withTicks,
    without: run.without });
};

const checkProgram = (out, program, index, { control, cap }) => {
  const has = kinds(program);
  for (const mutant of modelsFor(control)) {
    for (const readings of readingsFor(has)) {
      const where = { index, model: mutant ?? "base", readings,
        clock: has.has("clock"), program };
      recordRun(out, compareRun(program, mutant, readings, cap), where);
    }
  }
};

// The programs the tier explores without ticks, each with its generator
// index, which counts every program.
const selected = function* (bounds) {
  let index = -1;
  for (const program of model.programs(bounds)) {
    index += 1;
    if (dropsTicks(program)) yield [index, program];
  }
};

// A worker's share: the selected programs whose position among the
// selected is congruent to the worker's index. Sharing by generator
// index instead left most of the slow programs on a few workers.
const share = function* ({ bounds, count, index }) {
  let position = -1;
  for (const entry of selected(bounds)) {
    position += 1;
    if (position % count === index) yield entry;
  }
};

const runShare = (job) => {
  const out = { programs: 0, leavesChanged: 0, capped: [], diffs: [] };
  const started = Date.now();
  for (const [index, program] of share(job)) {
    out.programs += 1;
    checkProgram(out, program, index, job);
    // Through the main thread: a worker's own stderr stays buffered until
    // the worker yields, which this loop never does.
    const secs = Math.round((Date.now() - started) / 1000);
    parentPort.postMessage(
      { progress: `worker ${job.index} program ${index} ${secs} s\n` });
  }
  return out;
};

const merge = (a, b) => ({
  programs: a.programs + b.programs,
  leavesChanged: a.leavesChanged + b.leavesChanged,
  capped: [...a.capped, ...b.capped],
  diffs: [...a.diffs, ...b.diffs],
});

const startWorker = (job) => {
  const runWorker = (resolve, reject) => {
    const worker = new Worker(new URL(import.meta.url), { workerData: job,
      resourceLimits: { maxOldGenerationSizeMb: 6144 } });
    const onMessage = (message) => message.progress === undefined
      ? resolve(message.result) : process.stderr.write(message.progress);
    worker.on("message", onMessage);
    worker.on("error", reject);
  };
  return new Promise(runWorker);
};

const startWorkers = (args) => {
  const jobs = [];
  for (let index = 0; index < args.count; index += 1) {
    jobs.push(startWorker({ ...args, index }));
  }
  return Promise.all(jobs);
};

// The arguments as typed, with the defaults for workers and cap.
const rawArgs = (argv) => {
  const control = argv[0] === "control";
  const rest = control ? argv.slice(1) : argv;
  const [fibers, statements, ops, count, cap] = rest;
  return { control, fibers, statements, ops,
    count: count ?? String(availableParallelism()),
    cap: cap ?? "300000" };
};

const parseArgs = (raw) => ({ control: raw.control,
  bounds: { fibers: Number(raw.fibers),
    statements: Number(raw.statements), ops: Number(raw.ops) },
  count: Number(raw.count), cap: Number(raw.cap) });

// The strings, not their coercion: Number("") and Number(" ") are 0. A
// fractional count would start fewer workers than the share's modulus
// assumes, and the programs in between would go unexplored. Long digit
// strings convert to Infinity or round, so the value must be safe too.
const natural = (s) => typeof s === "string" && /^[0-9]+$/.test(s) &&
  Number.isSafeInteger(Number(s));
const positive = (s) => natural(s) && Number(s) > 0;

// Malformed bounds would make the generator yield nothing, or one empty
// program, and the check would hold vacuously.
const valid = (raw) => positive(raw.fibers) &&
  positive(raw.statements) && natural(raw.ops) &&
  positive(raw.count) && positive(raw.cap);

const USAGE = "usage: node tick.check.mjs [control] <fibers> <statements>" +
  " <ops> [workers] [cap]\n  fibers, statements, workers and cap must" +
  " be positive integers; ops a non-negative integer\n";

const show = (value) => JSON.stringify(value);

const printDiff = (d) => {
  console.log(`DIFFERENT ${d.model} readings ${show(d.readings)}: ` +
    `with ticks ${show(d.withTicks)}, without ${show(d.without)}`);
  console.log(`  program ${d.index} ${show(d.program)}`);
};

const printCapped = (c) => console.log(`OVER THE CAP ${c.model} ` +
  `readings ${show(c.readings)}: program ${c.index} ${show(c.program)}`);

const byProgram = (a, b) => a.index - b.index;
const inClockProgram = (d) => d.clock;

const verdictLine = (control, total) => {
  const differs = total.diffs.length > 0;
  if (control) {
    return differs ? "control failed, as it must"
      : "CONTROL PASSED: the check cannot fail";
  }
  return differs || total.capped.length > 0 ? "ticks: FAILED"
    : "ticks: holds";
};

const report = (args, total) => {
  total.diffs.sort(byProgram).forEach(printDiff);
  total.capped.sort(byProgram).forEach(printCapped);
  const clocked = total.diffs.filter(inClockProgram).length;
  console.log(`== bounds ${show(args.bounds)}: ${total.programs} ` +
    `programs without ticks in the tier, ticks changed the leaf count ` +
    `in ${total.leavesChanged} runs, ${total.capped.length} runs over ` +
    `the cap, ${total.diffs.length} runs different (${clocked} in ` +
    `programs with a clock read)`);
  const line = verdictLine(args.control, total);
  console.log(line);
  const ok = args.control ? total.diffs.length > 0 : line === "ticks: holds";
  return ok ? 0 : 1;
};

const main = async () => {
  const raw = rawArgs(process.argv.slice(2));
  if (!valid(raw)) {
    process.stderr.write(USAGE);
    process.exitCode = 2;
    return;
  }
  const args = parseArgs(raw);
  const started = Date.now();
  const code = report(args, (await startWorkers(args)).reduce(merge));
  const secs = Math.round((Date.now() - started) / 1000);
  process.stderr.write(`${secs} s on ${args.count} workers\n`);
  // Not process.exit: it would cut off stdout still draining into a pipe.
  process.exitCode = code;
};

if (isMainThread) await main();
else parentPort.postMessage({ result: runShare(workerData) });
