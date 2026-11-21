// Model of the one-pending-operation guard (copied semantics from restate-effect invocation.js)
// with a durable Clock.sleep, run under real Effect 4.1.5 race/timeout.
import { Clock, Effect } from "../../spike/node_modules/effect/dist/index.js"
let pending = false
const execute = (label, ms) => Effect.callback((resume) => {
  (async () => {
    if (pending) throw new Error(`guard: second durable op (${label})`)
    pending = true
    try { await new Promise((r) => setTimeout(r, ms)); return label } finally { pending = false }
  })().then((v) => resume(Effect.succeed(v)), (e) => resume(Effect.die(e)))
})
const durableClock = {
  currentTimeMillisUnsafe: () => 0, currentTimeMillis: Effect.succeed(0),
  currentTimeNanosUnsafe: () => 0n, currentTimeNanos: Effect.succeed(0n),
  monotonicTimeNanosUnsafe: () => 0n, monotonicTimeNanos: Effect.succeed(0n),
  sleep: (d) => execute(`sleep ${d}`, 5)
}
const runStep = (name, ms) => execute(`run ${name}`, ms)
const cases = {
  "Effect.timeout(run 50ms, 10ms)": Effect.timeout(runStep("a", 50), "10 millis"),
  "Effect.race(run a, run b)": Effect.race(runStep("a", 20), runStep("b", 5)),
  "Effect.race(run a 50ms, sleep 10ms then fallback)": Effect.race(runStep("a", 50), Effect.sleep("10 millis").pipe(Effect.as("timed out fallback"))),
}
for (const [label, eff] of Object.entries(cases)) {
  pending = false
  const exit = await Effect.runPromiseExit(eff.pipe(Effect.provideService(Clock.Clock, durableClock)))
  console.log(label, "=>", exit._tag, exit._tag === "Success" ? exit.value : String(exit.cause).split("\n")[0])
}
