// Random walks of the base model through every predicate; prints each failing
// predicate with a count and its first message.
//   node tools/random-walks.mjs [walks=20000] [statements=3]
import * as model from "../model.mjs";
import { predicates } from "../predicates.mjs";
const N = Number(process.argv[2] ?? 20000);
const bounds = { fibers: 2, statements: Number(process.argv[3] ?? 3), ops: 3 };
let seed = 7; const rnd = () => { seed = (seed * 1103515245 + 12345) & 0x7fffffff; return seed / 0x80000000; };
const progs = [...model.programs(bounds)];
const fails = new Map(); let n = 0, errors = 0;
for (let i = 0; i < N; i++) {
  const p = progs[Math.floor(rnd() * progs.length)];
  let s = model.initial(p, {});
  try {
    for (let c = model.choices(s); c.length; c = model.choices(s)) s = model.step(s, c[Math.floor(rnd() * c.length)]);
    const h = model.history(s); n++;
    for (const pr of predicates) { let v; try { v = pr.check(h); } catch (e) { v = { msg: "THREW " + e.message }; }
      if (v) { const f = fails.get(pr.id) ?? { count: 0, ex: v.msg, prog: p }; f.count++; fails.set(pr.id, f); } }
  } catch (e) { errors++; }
}
console.log(`programs ${progs.length}, walks ${n}, model errors ${errors}`);
for (const [id, f] of [...fails].sort((a, b) => b[1].count - a[1].count)) console.log(id.padEnd(8), String(f.count).padStart(6), f.ex.slice(0, 150));
