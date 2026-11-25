// Judges every mutant's witness (witnesses.mjs): the base model's history must
// pass every predicate and the mutant's must fail at least one.
//   node tools/judge-witnesses.mjs
import { mutantWitnesses, replayWitness } from "../witnesses.mjs";
import { predicates } from "../predicates.mjs";
const fails = (h) => predicates.filter((p) => p.check(h)).map((p) => p.id);
for (const m of Object.keys(mutantWitnesses)) {
  const base = fails(replayWitness(m, {})), mut = fails(replayWitness(m, { mutant: m }));
  console.log(m.padEnd(20), "base:", base.join(",") || "clean", "| mutant:", mut.join(",") || "NOT CAUGHT");
}
