// Checks that merging hides nothing (issue #48, step 7). On small
// programs, under the base model and under every mutant, the merged search
// (merged.mjs, monitors) must report exactly the statements that a full,
// unmerged search reports when it judges every history with the history
// predicates (predicates.mjs). Exits 1 on any difference.
//
//   FREEZE=1 node merged.check.mjs [programs] [nodeCap]
// Run it with FREEZE=1, so monitor states are deep-frozen and any write
// to a shared state throws. UNSOUND_KEY=1 is its control and must exit 1.
import * as model from "./model.mjs";
import { predicates } from "./predicates.mjs";
import { explore } from "./merged.mjs";
import { mutantWitnesses } from "./witnesses.mjs";

const programCount = Number(process.argv[2] ?? 12);
const cap = Number(process.argv[3] ?? 400_000);
const options = (mutant) => ({ mutant, limits: { readings: [0] } });

// Every history of one program, unmerged; returns failing ids or null if capped.
const unmergedFailures = (program, opts) => {
  const failing = new Set();
  const stack = [model.initial(program, opts)];
  let visited = 0;
  while (stack.length > 0) {
    if ((visited += 1) > cap) return null;
    const state = stack.pop();
    const next = model.choices(state);
    if (next.length > 0) { for (const c of next) stack.push(model.step(state, c)); continue; }
    const history = model.history(state);
    for (const p of predicates) if (p.check(history) !== null) failing.add(p.id);
  }
  return failing;
};

const sameSet = (a, b) => a.size === b.size && [...a].every((x) => b.has(x));

// A fixed spread of small programs: every k-th program at 2 statements.
const pick = () => {
  const all = [...model.programs({ fibers: 2, statements: 2, ops: 2 })];
  const stride = Math.max(1, Math.floor(all.length / programCount));
  return all.filter((_, i) => i % stride === 0).slice(0, programCount);
};

let differences = 0;
let compared = 0;
let withFailures = 0;
let skipped = 0;
// Small programs under every model, plus each mutant's witness program
// under the base model and that mutant, where a failure is known to exist.
const pairs = [
  ...pick().flatMap((program) => [undefined, ...Object.keys(model.MUTANTS)]
    .map((mutant) => [program, mutant])),
  ...Object.entries(mutantWitnesses).flatMap(([mutant, w]) =>
    [[w.program, undefined], [w.program, mutant]]),
];
for (const [program, mutant] of pairs) {
  {
    const full = unmergedFailures(program, options(mutant));
    if (full === null) { skipped += 1; continue; }
    const merged = explore(program, options(mutant));
    const got = new Set(merged.failures.keys());
    compared += 1;
    if (full.size > 0) withFailures += 1;
    if (!sameSet(full, got)) {
      differences += 1;
      console.log("DIFFERENT", mutant ?? "base", JSON.stringify(program),
        "unmerged:", [...full].join(",") || "none",
        "merged:", [...got].join(",") || "none");
    }
  }
}
console.log(`compared ${compared} (program, model) pairs, ${withFailures} with failures, ` +
  `skipped ${skipped} over the cap, ${differences} different`);
process.exit(differences === 0 && compared > 0 ? 0 : 1);
