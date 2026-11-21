// Checks that Effect 4.1.5 lets a run action reset Clock and Random to the defaults, and that
// fibers forked by the action (child, detached, forkIn an outer scope) and its finalizers see
// the defaults, not the handler's deterministic services.
import { Clock, Effect, Random, Scope, Fiber, Exit } from "../../spike/node_modules/effect/dist/index.js"
const seen = []
const durableClock = {
  currentTimeMillisUnsafe: () => { seen.push("DURABLE read"); return 1 }, currentTimeMillis: Effect.sync(() => { seen.push("DURABLE read"); return 1 }),
  currentTimeNanosUnsafe: () => { seen.push("DURABLE read"); return 1n }, currentTimeNanos: Effect.sync(() => 1n),
  monotonicTimeNanosUnsafe: () => { seen.push("DURABLE read"); return 1n }, monotonicTimeNanos: Effect.sync(() => 1n),
  sleep: () => Effect.sync(() => seen.push("DURABLE sleep"))
}
const resetDefaults = (eff) => eff.pipe(
  Effect.provideService(Clock.Clock, Clock.Clock.defaultValue()),
  Effect.provideService(Random.Random, Random.Random.defaultValue()))
const probe = (tag) => Effect.gen(function* () {
  const t = yield* Clock.currentTimeMillis
  yield* Effect.sleep("1 millis")
  const r = yield* Random.next
  seen.push(`${tag}: time=${t > 1e12 ? "real" : t} random=${r.toFixed(3)}`)
})
const program = Effect.gen(function* () {
  const outer = yield* Scope.make()
  const action = Effect.gen(function* () {
    yield* probe("action")
    const c = yield* Effect.forkChild(probe("forkChild"))
    yield* Fiber.join(c)
    const d = yield* Effect.forkDetach(probe("forkDetach"))
    yield* Fiber.join(d)
    const o = yield* Effect.forkIn(probe("forkIn outer scope"), outer)
    yield* Fiber.join(o)
    yield* Effect.addFinalizer(() => probe("finalizer"))
  }).pipe(Effect.scoped)
  yield* resetDefaults(action)
  yield* probe("handler after run")
}).pipe(Effect.provideService(Clock.Clock, durableClock), Random.withSeed("inv-1"))
await Effect.runPromise(program)
console.log(seen.join("\n"))
