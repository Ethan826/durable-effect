// The exhaustive tier of the step 7 check (issue #48), run in parallel.
// Every program within the bounds is explored with merged.mjs under the
// published schedule, with two reductions: one clock reading except in
// the clock tier (slice.check.mjs readings), and no ticks for programs
// with no run that lack a sleep or a clock read (ticks.mjs, issue #49).
// tick.check.mjs checks that reduction by verdicts: see README.md.
//
//   node tier.mjs <fibers> <statements> <ops> [workers] [nodeCap] [tier]
//   tier: "main" (readings {0}) or "clock" (readings {0, 2, 3}, programs
//   with a sleep or a clock read only)
//
// Prints one line per failing monitor with its first witness, the
// boundary coverage, programs over the node cap, and the totals; exits 1
// on any failure or any program over the cap.
import { Worker, isMainThread, parentPort, workerData } from "node:worker_threads";
import { availableParallelism } from "node:os";
import * as model from "./model.mjs";
import { explore } from "./merged.mjs";
import { boundaries } from "./predicates.mjs";
import { dropsTicks } from "./ticks.mjs";

const statementsOf = (stmts) => stmts.flatMap((s) =>
  [s, ...statementsOf(s.body ?? []), ...statementsOf(s.finalizer ?? [])]);
const kinds = (program) => new Set(program.fibers
  .flatMap((f) => statementsOf(f.body)).map((s) => s.s));

const limitsFor = (program, tier) => ({
  readings: tier === "clock" ? [0, 2, 3] : [0],
  ...(dropsTicks(program) ? { ticks: 0 } : {}),
});

const inTier = (program, tier) => tier !== "clock" ||
  kinds(program).has("sleep") || kinds(program).has("clock");

const runShare = ({ bounds, tier, cap, index, count }) => {
  const out = { programs: 0, nodes: 0, leaves: 0, failures: {}, capped: [],
    boundaries: {} };
  let i = -1;
  for (const program of model.programs(bounds)) {
    i += 1;
    if (i % count !== index || !inTier(program, tier)) continue;
    out.programs += 1;
    const tally = (state) => {
      for (const tag of boundaries(model.history(state))) {
        out.boundaries[tag] = (out.boundaries[tag] ?? 0) + 1;
      }
    };
    const r = explore(program, { limits: limitsFor(program, tier) }, cap, tally);
    out.nodes += r.nodes;
    out.leaves += r.leaves;
    if (r.capped) out.capped.push(program);
    for (const [id, { verdict, path }] of r.failures) {
      out.failures[id] ??= { count: 0, msg: verdict.msg, program, path };
      out.failures[id].count += 1;
    }
  }
  return out;
};

const merge = (a, b) => {
  a.programs += b.programs; a.nodes += b.nodes; a.leaves += b.leaves;
  a.capped.push(...b.capped);
  for (const [id, f] of Object.entries(b.failures)) {
    if (a.failures[id]) a.failures[id].count += f.count; else a.failures[id] = f;
  }
  for (const [tag, n] of Object.entries(b.boundaries)) {
    a.boundaries[tag] = (a.boundaries[tag] ?? 0) + n;
  }
  return a;
};

const main = async () => {
  const [fibers, statements, ops] = process.argv.slice(2, 5).map(Number);
  const count = Number(process.argv[5] ?? availableParallelism());
  const cap = Number(process.argv[6] ?? 2_000_000);
  const tier = process.argv[7] ?? "main";
  const bounds = { fibers, statements, ops };
  const started = Date.now();
  const shares = await Promise.all(Array.from({ length: count }, (_, index) =>
    new Promise((resolve, reject) => {
      const worker = new Worker(new URL(import.meta.url),
        { workerData: { bounds, tier, cap, index, count },
          resourceLimits: { maxOldGenerationSizeMb: 6144 } });
      worker.on("message", resolve);
      worker.on("error", reject);
    })));
  const total = shares.reduce(merge);
  const seconds = Math.round((Date.now() - started) / 1000);
  console.log(`== tier ${tier}, bounds ${JSON.stringify(bounds)}: ${total.programs} programs, ` +
    `${total.nodes} nodes, ${total.leaves} leaves, ${seconds} s on ${count} workers`);
  for (const [id, f] of Object.entries(total.failures)) {
    console.log(`FAIL ${id} in ${f.count} programs: ${f.msg}`);
    console.log(`  program ${JSON.stringify(f.program)}`);
    console.log(`  path ${JSON.stringify(f.path)}`);
  }
  console.log(`over the node cap: ${total.capped.length}`);
  for (const p of total.capped.slice(0, 5)) console.log(`  ${JSON.stringify(p)}`);
  console.log("boundaries:", JSON.stringify(total.boundaries));
  const ok = Object.keys(total.failures).length === 0 && total.capped.length === 0;
  console.log(ok ? "TIER PASSES" : "TIER FAILS");
  process.exit(ok ? 0 : 1);
};

if (isMainThread) await main();
else parentPort.postMessage(runShare(workerData));
