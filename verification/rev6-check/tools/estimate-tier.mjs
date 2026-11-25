// Estimates the cost of the 3-statement tier from a seeded sample of programs,
// with the tier's limits (readings {0}; no ticks without a run), on workers.
//   node tools/estimate-tier.mjs [sample=100] [workers=8] [nodeCap=3e6]
// Estimates the 3-statement tier: explores a seeded random sample of programs
// with the tier's limits and reports nodes and seconds per program.
import { Worker, isMainThread, parentPort, workerData } from "node:worker_threads";
import * as model from "../model.mjs";
import { explore } from "../merged.mjs";
const stmts = (ss) => ss.flatMap((s) => [s, ...stmts(s.body ?? []), ...stmts(s.finalizer ?? [])]);
const hasRun = (p) => p.fibers.some((f) => stmts(f.body).some((s) => s.s === "run"));
if (isMainThread) {
  const all = [...model.programs({ fibers: 2, statements: 3, ops: 3 })];
  let seed = 48; const rnd = () => { seed = (seed * 1103515245 + 12345) & 0x7fffffff; return seed / 0x80000000; };
  const sample = Array.from({ length: Number(process.argv[2] ?? 100) }, () => all[Math.floor(rnd() * all.length)]);
  const W = Number(process.argv[3] ?? 8), cap = Number(process.argv[4] ?? 3e6);
  const parts = await Promise.all(Array.from({ length: W }, (_, i) => new Promise((res, rej) => {
    const w = new Worker(new URL(import.meta.url), { workerData: { progs: sample.filter((_, k) => k % W === i), cap }, resourceLimits: { maxOldGenerationSizeMb: 6144 } });
    w.on("message", res); w.on("error", rej); })));
  const rows = parts.flat().sort((a, b) => b.s - a.s);
  const tot = rows.reduce((a, r) => a + r.s, 0);
  console.log(`programs ${all.length}, sampled ${rows.length}, mean ${(tot / rows.length).toFixed(1)} core-s, capped ${rows.filter((r) => r.capped).length}, failures ${rows.filter((r) => r.f.length).length}`);
  console.log(`estimate for all: ${Math.round(tot / rows.length * all.length / 3600)} core-hours`);
  for (const r of rows.slice(0, 5)) console.log(`  ${r.s.toFixed(0)}s ${r.nodes} nodes ${r.capped ? "CAPPED " : ""}${r.f.join(",")} ${JSON.stringify(r.p).slice(0, 160)}`);
} else {
  parentPort.postMessage(workerData.progs.map((p) => { const t = Date.now();
    const r = explore(p, { limits: { readings: [0], ...(hasRun(p) ? {} : { ticks: 0 }) } }, workerData.cap);
    return { p, s: (Date.now() - t) / 1000, nodes: r.nodes, capped: r.capped, f: [...r.failures.keys()] }; }));
}
