import { Clock, Effect } from "../../spike/node_modules/effect/dist/index.js"
let pending = false
const execute = (label, ms) => Effect.callback((resume) => {
  (async () => {
    if (pending) throw new Error(`guard: second durable op (${label})`)
    pending = true
    try { await new Promise((r) => setTimeout(r, ms)); return label } finally { pending = false }
  })().then((v) => resume(Effect.succeed(v)), (e) => resume(Effect.die(e)))
})
const runStep = (name, ms) => execute(`run ${name}`, ms)
const cases = {
  "Effect.all(mode result, concurrency 2)": Effect.all([runStep("a", 20), runStep("b", 5)], { concurrency: 2, mode: "result" }),
  "Effect.raceAll([a,b,c])": Effect.raceAll([runStep("a", 20), runStep("b", 5), runStep("c", 5)]),
}
for (const [label, eff] of Object.entries(cases)) {
  pending = false
  const exit = await Effect.runPromiseExit(eff)
  console.log(label, "=>", exit._tag, exit._tag === "Success" ? JSON.stringify(exit.value) : String(exit.cause).split("\n")[0])
}
