// Does a run action executed restate-effect-style (Effect.context() minus invocation services,
// then runPromiseExitWith) inherit the handler's replaced Clock and seeded Random?
import { Clock, Context, Effect, Random } from "../../spike/node_modules/effect/dist/index.js"
class Invocation extends Context.Service()("Invocation") {}
const durableClock = {
  currentTimeMillisUnsafe: () => 42, currentTimeMillis: Effect.succeed(42),
  currentTimeNanosUnsafe: () => 42000000n, currentTimeNanos: Effect.succeed(42000000n),
  monotonicTimeNanosUnsafe: () => 42000000n, monotonicTimeNanos: Effect.succeed(42000000n),
  sleep: (d) => Effect.sync(() => console.log("DURABLE SLEEP called inside run action", d.toString()))
}
const action = Effect.gen(function* () {
  const now = yield* Clock.currentTimeMillis
  const r = yield* Random.next
  yield* Effect.sleep("10 millis")
  return { now, r }
})
const handler = Effect.gen(function* () {
  const ctx = yield* Effect.context()
  const isolated = Context.omit(Invocation)(ctx)
  const exit = yield* Effect.promise(() => Effect.runPromiseExitWith(isolated)(action))
  const after = yield* Random.next
  return { exit: exit._tag === "Success" ? exit.value : exit, handlerDrawAfter: after }
})
const run = (label) => Effect.runPromise(handler.pipe(
  Effect.provideService(Clock.Clock, durableClock),
  Random.withSeed("inv-1"),
  Effect.provideService(Invocation, {}))).then((v) => console.log(label, JSON.stringify(v)))
await run("original")
// Replay: the run action is skipped (journaled); the handler's next draw:
const replay = Effect.gen(function* () { return { handlerDrawAfter: yield* Random.next } })
console.log("replay", JSON.stringify(await Effect.runPromise(replay.pipe(Random.withSeed("inv-1")))))
