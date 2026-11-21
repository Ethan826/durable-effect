// The guard allows concurrency as long as at most one fiber awaits a durable operation.
// Here one fiber awaits a single durable run while a second, purely non-durable fiber (only
// yields) reads Clock and Random. Neither the guard nor the sticky rule fires. Live, the durable
// run is slow (30 ms); on replay it resolves from the journal in two ticks. The fibers' order of
// Clock reads and Random draws swaps, so the handler sees different values on replay.
import { Clock, Effect, Random } from "../../spike/node_modules/effect/dist/index.js"

const makeExecutor = (journal) => {
  const st = { i: 0, pending: 0, violation: undefined }
  let L = 1000
  const durable = (name, liveMs, liveSample) => Effect.suspend(() => {
    if (st.violation) return Effect.die("sticky")
    if (st.pending > 0) { st.violation = "two pending"; return Effect.die("two pending") }
    const idx = st.i
    st.i += 2 // completion entry + sample entry
    st.pending++
    return Effect.callback((resume) => {
      let settled = false
      const done = (s) => { settled = true; st.pending--; L = Math.max(L, s); resume(Effect.succeed(name)) }
      if (idx < journal.length) setImmediate(() => setImmediate(() => done(journal[idx + 1])))
      else setTimeout(() => { journal[idx] = name; journal[idx + 1] = liveSample; done(liveSample) }, liveMs)
      return Effect.sync(() => { if (!settled) { st.pending--; st.violation ??= "abandoned" } })
    })
  })
  const nanos = () => BigInt(L) * 1000000n
  const clock = {
    currentTimeMillisUnsafe: () => L, currentTimeMillis: Effect.sync(() => L),
    currentTimeNanosUnsafe: nanos, currentTimeNanos: Effect.sync(nanos),
    monotonicTimeNanosUnsafe: nanos, monotonicTimeNanos: Effect.sync(nanos),
    sleep: () => Effect.die("not used")
  }
  return { st, clock, durable }
}

const yields = (n) => Effect.gen(function* () { for (let k = 0; k < n; k++) yield* Effect.yieldNow })

const handler = (durable) => Effect.all([
  durable("run a", 30, 1030).pipe(Effect.andThen(Random.next), Effect.map((r) => `A draws ${r.toFixed(3)}`)),
  yields(50).pipe(Effect.andThen(Effect.all([Random.next, Clock.currentTimeMillis])),
    Effect.map(([r, t]) => `B draws ${r.toFixed(3)}, reads L=${t}`))
], { concurrency: "unbounded" })

const runAttempt = async (journal) => {
  const { st, clock, durable } = makeExecutor(journal)
  const out = await Effect.runPromise(handler(durable).pipe(
    Effect.provideService(Clock.Clock, clock), Random.withSeed("invocation-id")))
  return { out, violation: st.violation ?? "none" }
}
const journal = []
console.log("attempt 1 (live):  ", await runAttempt(journal))
console.log("attempt 2 (replay):", await runAttempt(journal))
