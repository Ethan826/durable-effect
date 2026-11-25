// Finds, by random walks, the smallest history a predicate rejects and prints
// its program, traces and journals.
//   node tools/smallest-witness.mjs <predicateId> [walks=20000]
import * as model from "../model.mjs";
import { predicates } from "../predicates.mjs";
import { writeFileSync } from "node:fs";
const want = process.argv[2], N = Number(process.argv[3] ?? 20000);
let seed = 7; const rnd = () => { seed = (seed * 1103515245 + 12345) & 0x7fffffff; return seed / 0x80000000; };
const progs = [...model.programs({ fibers: 2, statements: 3, ops: 3 })];
const pr = predicates.find((p) => p.id === want); let best = null;
for (let i = 0; i < N; i++) {
  const p = progs[Math.floor(rnd() * progs.length)]; let s = model.initial(p, {});
  for (let c = model.choices(s); c.length; c = model.choices(s)) s = model.step(s, c[Math.floor(rnd() * c.length)]);
  const h = model.history(s); const v = pr.check(h);
  if (v) { const size = h.attempts.reduce((a, x) => a + x.trace.length, 0); if (!best || size < best.size) best = { size, v, h }; }
}
const file = `./w-${want}.json`;
writeFileSync(file, JSON.stringify(best, null, 1));
console.log(want, "size", best?.size, best?.v.msg, JSON.stringify(best?.v.detail ?? "").slice(0, 300));
console.log("program", JSON.stringify(best?.h.program));
for (const a of best?.h.attempts ?? []) { console.log(`-- attempt ${a.n} end ${JSON.stringify(a.end)}`); for (const e of a.trace) console.log("  ", JSON.stringify(e)); console.log("   journalOut", a.journalOut.map((e) => e.e === "cmd" ? `${e.idx}:cmd:${e.cmd.c}:${e.cmd.op ?? ""}` : e.e === "notif" ? `${e.idx}:notif(${e.of})=${JSON.stringify(e.value)}` : `${e.idx}:${e.e}`).join(" ")); console.log("   effects", JSON.stringify(a.effects)); }
