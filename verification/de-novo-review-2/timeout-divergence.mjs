// Models the design's executor rules (one pending durable op, abandonment by interruption is a
// violation, violations stick) with a fake journal, and runs Effect.timeoutOption from effect
// 4.1.5 around pure Effect work (no Date, no timers, no randomness: only yields).
// Attempt 1 is live: the durable timer runs on a real timer. Attempt 2 replays the journal, as
// after a retry or a suspension: the timer's completion is already journaled.
import { Clock, Duration, Effect, Exit, Option } from "../../spike/node_modules/effect/dist/index.js"

const makeExecutor = (journal) => {
  const st = { i: 0, pending: 0, violation: undefined, log: [] }
  const violate = (why) => { st.violation ??= why; st.log.push("VIOLATION " + why) }
  // A durable operation: replayed if the journal has it, else live (resolves after `liveMs`).
  const durable = (name, liveMs) => Effect.suspend(() => {
    if (st.violation) return Effect.die("sticky: " + st.violation)
    if (st.pending > 0) { violate("two pending"); return Effect.die("two pending") }
    const idx = st.i++
    st.pending++
    return Effect.callback((resume) => {
      const done = () => { st.pending--; settled = true; resume(Effect.void) }
      let settled = false
      if (idx < journal.length) { st.log.push(`replay ${name}`); setImmediate(() => setImmediate(done)) }
      else { st.log.push(`live ${name}`); setTimeout(() => { journal[idx] = name; done() }, liveMs) }
      // Interruption of the awaiting fiber is abandonment.
      return Effect.sync(() => { if (!settled) { st.pending--; violate("abandoned " + name) } })
    })
  })
  let L = 1000
  const clock = {
    currentTimeMillisUnsafe: () => L, currentTimeMillis: Effect.sync(() => L),
    currentTimeNanosUnsafe: () => BigInt(L) * 1000000n, currentTimeNanos: Effect.sync(() => BigInt(L) * 1000000n),
    monotonicTimeNanosUnsafe: () => BigInt(L) * 1000000n, monotonicTimeNanos: Effect.sync(() => BigInt(L) * 1000000n),
    sleep: (d) => {
      const ms = Duration.toMillis(d)
      if (ms <= 0) return Effect.yieldNow
      if (!Number.isFinite(ms)) return Effect.never
      // the sleep, then its sample: two durable operations in sequence
      return durable(`sleep(${Math.ceil(ms)})`, Math.ceil(ms)).pipe(
        Effect.andThen(durable("sample", 1)),
        Effect.andThen(Effect.sync(() => { L += Math.ceil(ms) })))
    }
  }
  return { st, clock }
}

// Pure work: N yields. No time, no randomness, no timers.
const work = (n) => Effect.gen(function* () { for (let k = 0; k < n; k++) yield* Effect.yieldNow; return "work-done" })

const handler = Effect.gen(function* () {
  const r = yield* Effect.timeoutOption(work(Number(process.argv[2] ?? 300)), "40 millis")
  return Option.isSome(r) ? "branch: work finished" : "branch: timed out"
})

const runAttempt = async (journal) => {
  const { st, clock } = makeExecutor(journal)
  const t0 = performance.now()
  const exit = await Effect.runPromiseExit(handler.pipe(Effect.provideService(Clock.Clock, clock)))
  const final = st.violation ? `DEFECT (sticky violation: ${st.violation})` : Exit.isSuccess(exit) ? exit.value : String(exit)
  return { final, log: st.log, ms: (performance.now() - t0).toFixed(1) }
}

const journal = []
const a1 = await runAttempt(journal)
console.log("attempt 1 (live):  ", a1.final, a1.log, a1.ms + "ms")
// The live timer keeps running after attempt 1 ends (as Restate's timer would) and is journaled.
await new Promise((r) => setTimeout(r, 100))
console.log("journal after attempt 1:", journal)
const a2 = await runAttempt(journal)
console.log("attempt 2 (replay):", a2.final, a2.log, a2.ms + "ms")
