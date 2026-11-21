// G2 says a deterministic service used from a non-root fiber "fails the same way in every
// attempt" because the fiber is forked at the same program point. The violation's timing
// relative to the root's durable operations is not fixed. Here a child does pure work and then
// reads Clock. Live, the root's durable op is pending for 40 ms and the child's read happens:
// violation. On replay (the retry after that defect) the op resolves in two ticks, the root
// returns, the child is interrupted before its read, and the handler succeeds.
import { Clock, Effect, Fiber, Exit } from "../../spike/node_modules/effect/dist/index.js"
const runAttempt = async (journal) => {
  const st = { root: undefined, violations: [], i: 0 }
  const guard = (w) => { if (Fiber.getCurrent() !== st.root) st.violations.push(w) }
  const nanos = () => { guard("clock"); return 1n }
  const clock = { currentTimeMillisUnsafe: () => { guard("clock"); return 1 }, currentTimeMillis: Effect.sync(() => { guard("clock"); return 1 }),
    currentTimeNanosUnsafe: nanos, currentTimeNanos: Effect.sync(nanos), monotonicTimeNanosUnsafe: nanos, monotonicTimeNanos: Effect.sync(nanos), sleep: () => Effect.die("unused") }
  const durable = (name, liveMs) => Effect.suspend(() => {
    guard("durable " + name)
    const idx = st.i++
    return Effect.callback((resume) => {
      if (idx < journal.length) setImmediate(() => setImmediate(() => resume(Effect.void)))
      else setTimeout(() => { journal[idx] = name; resume(Effect.void) }, liveMs)
    })
  })
  const pure = (n) => Effect.forEach(Array.from({ length: n }, (_, k) => k), () => Effect.void, { discard: true })
  const handler = Effect.gen(function* () {
    st.root = Fiber.getCurrent()
    yield* Effect.forkChild(pure(20000).pipe(Effect.andThen(Clock.currentTimeMillis)))
    yield* durable("run a", 40)
    return "ok"
  }).pipe(Effect.provideService(Clock.Clock, clock))
  const exit = await Effect.runPromiseExit(handler)
  return { exit: exit._tag, violations: st.violations }
}
const journal = []
console.log("attempt 1 (live):  ", JSON.stringify(await runAttempt(journal)))
console.log("attempt 2 (replay):", JSON.stringify(await runAttempt(journal)))
