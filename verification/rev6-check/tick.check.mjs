// tick.check.mjs: checks by verdicts the reduction that tier.mjs explores
// programs without a run with no ticks. For every program without a run
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
//     only CONTROL_MUTANTS.hostTime, whose clock statement reads host
//     time; exits 0 only if some run differs, which shows the check can
//     fail. It needs 3 statements: seeing time pass needs a sleep, an
//     await and a clock read, since a turn is atomic.
//
// As in tier.mjs, program i of the generator (counting programs with a
// run) goes to worker i % workers, and i names it in the output. Results
// are merged in worker order and then sorted by program, so stdout does
// not depend on scheduling. Progress goes to stderr.
import {
  Worker, isMainThread, parentPort, workerData,
} from "node:worker_threads";
import { availableParallelism } from "node:os";
import * as model from "./model.mjs";
import { explore } from "./merged.mjs";

const statementsOf = (stmts) => stmts.flatMap((s) =>
  [s, ...statementsOf(s.body ?? []), ...statementsOf(s.finalizer ?? [])]);
const kinds = (program) => new Set(program.fibers
  .flatMap((f) => statementsOf(f.body)).map((s) => s.s));

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

// A worker's share: generator index i with i % count === index, and no
// run. The index counts programs with a run too, as tier.mjs does.
const share = function* ({ bounds, count, index }) {
  let i = -1;
  for (const program of model.programs(bounds)) {
    i += 1;
    if (i % count !== index || kinds(program).has("run")) continue;
    yield [i, program];
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

const startWorker = (job) => new Promise((resolve, reject) => {
  const worker = new Worker(new URL(import.meta.url), { workerData: job,
    resourceLimits: { maxOldGenerationSizeMb: 6144 } });
  const onMessage = (message) => message.progress === undefined
    ? resolve(message.result) : process.stderr.write(message.progress);
  worker.on("message", onMessage);
  worker.on("error", reject);
});

const parseArgs = (argv) => {
  const control = argv[0] === "control";
  const rest = control ? argv.slice(1) : argv;
  const [fibers, statements, ops] = rest.slice(0, 3).map(Number);
  return { control, bounds: { fibers, statements, ops },
    count: Number(rest[3] ?? availableParallelism()),
    cap: Number(rest[4] ?? 300_000) };
};

// A fractional count would start fewer workers than the share's modulus
// assumes, and the programs in between would go unexplored.
const positive = (n) => Number.isInteger(n) && n > 0;

const USAGE = "usage: node tick.check.mjs [control] <fibers> <statements>" +
  " <ops> [workers] [cap]\n  workers and cap must be positive integers\n";

const show = (value) => JSON.stringify(value);

const printDiff = (d) => {
  console.log(`DIFFERENT ${d.model} readings ${show(d.readings)}: ` +
    `with ticks ${show(d.withTicks)}, without ${show(d.without)}`);
  console.log(`  program ${d.index} ${show(d.program)}`);
};

const printCapped = (c) => console.log(`OVER THE CAP ${c.model} ` +
  `readings ${show(c.readings)}: program ${c.index} ${show(c.program)}`);

const byProgram = (a, b) => a.index - b.index;

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
  const clocked = total.diffs.filter((d) => d.clock).length;
  console.log(`== bounds ${show(args.bounds)}: ${total.programs} ` +
    `programs without a run, ticks changed the leaf count in ` +
    `${total.leavesChanged} runs, ${total.capped.length} runs over the ` +
    `cap, ${total.diffs.length} runs different (${clocked} in programs ` +
    `with a clock read)`);
  const line = verdictLine(args.control, total);
  console.log(line);
  const ok = args.control ? total.diffs.length > 0 : line === "ticks: holds";
  return ok ? 0 : 1;
};

const main = async () => {
  const args = parseArgs(process.argv.slice(2));
  if (!positive(args.count) || !positive(args.cap)) {
    process.stderr.write(USAGE);
    process.exitCode = 2;
    return;
  }
  const started = Date.now();
  const shares = await Promise.all(Array.from({ length: args.count },
    (_, index) => startWorker({ ...args, index })));
  const code = report(args, shares.reduce(merge));
  const secs = Math.round((Date.now() - started) / 1000);
  process.stderr.write(`${secs} s on ${args.count} workers\n`);
  // Not process.exit: it would cut off stdout still draining into a pipe.
  process.exitCode = code;
};

if (isMainThread) await main();
else parentPort.postMessage({ result: runShare(workerData) });
