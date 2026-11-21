// A forked fiber that does only pure work and then interrupts the root (Fiber.interrupt is not
// a Clock, Random or durable operation, so the root-fiber rule allows it). Live, the durable op
// is pending for 40 ms, so the interrupt lands on it: abandonment, a violation (defect, retried).
// On replay the op resolves in two ticks, the interrupt lands on pure work in the root, and the
// handler exits interrupted with no violation, which the design treats as a cancellation.
import { Effect, Fiber, Exit, Cause } from "../../spike/node_modules/effect/dist/index.js"
const runAttempt = async (journal) => {
  const st = { root: undefined, violations: [], i: 0 }
  const durable = (name, liveMs) => Effect.suspend(() => {
    if (Fiber.getCurrent() !== st.root) st.violations.push("non-root " + name)
    const idx = st.i++
    let settled = false
    return Effect.callback((resume) => {
      const done = () => { settled = true; resume(Effect.void) }
      if (idx < journal.length) setImmediate(() => setImmediate(done))
      else setTimeout(() => { journal[idx] = name; done() }, liveMs)
      return Effect.sync(() => { if (!settled) st.violations.push("abandoned " + name) })
    })
  })
  const pure = (n) => Effect.forEach(Array.from({ length: n }, (_, k) => k), () => Effect.void, { discard: true })
  const handler = Effect.gen(function* () {
    st.root = Fiber.getCurrent()
    const root = st.root
    yield* Effect.forkDetach(pure(8000).pipe(Effect.andThen(Fiber.interrupt(root))))
    yield* durable("run a", 40)
    yield* pure(40000)
    return "done"
  })
  const exit = await Effect.runPromiseExit(handler)
  const kind = Exit.isSuccess(exit) ? "success" : Cause.hasInterruptsOnly(exit.cause) ? "interrupted (design: cancelled, terminal)" : "failure"
  return { exit: kind, violations: st.violations }
}
// The abandoned live op still completes on the server and is journaled; the retry replays it.
console.log("attempt 1 (live):  ", JSON.stringify(await runAttempt([])))
console.log("attempt 2 (replay):", JSON.stringify(await runAttempt(["run a"])))
