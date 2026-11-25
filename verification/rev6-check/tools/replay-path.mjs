// Replays a recorded choice path (as printed by tier.mjs) and prints the
// failing predicates, traces and journals.
//   node tools/replay-path.mjs '[program, path, options]'
import * as model from "../model.mjs";
import { predicates } from "../predicates.mjs";
const [prog, path, opts] = JSON.parse(process.argv[2]);
let s = model.initial(prog, opts); for (const c of path) s = model.step(s, c);
const h = model.history(s);
for (const p of predicates) { const v = p.check(h); if (v) console.log("FAIL", p.id, v.msg, JSON.stringify(v.detail).slice(0, 200)); }
for (const a of h.attempts) { console.log("-- attempt", a.n, JSON.stringify(a.end)); a.trace.forEach((e, i) => console.log("  ", i, JSON.stringify(e))); console.log("   journalOut", a.journalOut.map((e) => e.e === "cmd" ? `${e.idx}:${e.cmd.c}:${e.cmd.op ?? e.cmd.target ?? ""}` : e.e === "notif" ? `${e.idx}:n(${e.of})=${JSON.stringify(e.value)}` : `${e.idx}:${e.e}`).join(" ")); }
