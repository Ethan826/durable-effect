// Does building a Layer inside the handler (Effect.provide) read Clock/Random off the root?
import { Clock, Context, Effect, Fiber, Layer, Random } from "../../spike/node_modules/effect/dist/index.js"
const st = { root: undefined, reads: [] }
const rd = () => { const f = Fiber.getCurrent(); st.reads.push(f === st.root ? "root" : "OTHER"); return 1 }
const clock = { currentTimeMillisUnsafe: rd, currentTimeMillis: Effect.sync(rd), currentTimeNanosUnsafe: () => BigInt(rd()), currentTimeNanos: Effect.sync(() => BigInt(rd())),
  monotonicTimeNanosUnsafe: () => BigInt(rd()), monotonicTimeNanos: Effect.sync(() => BigInt(rd())), sleep: () => Effect.void }
class Svc extends Context.Service()("Svc") {}
const layer = Layer.effect(Svc, Effect.map(Clock.currentTimeMillis, (t) => ({ t })))
await Effect.runPromise(Effect.gen(function* () {
  st.root = Fiber.getCurrent()
  yield* Effect.provide(Effect.flatMap(Svc.asEffect ? Svc.asEffect() : Svc, (s) => Effect.succeed(s)), layer)
}).pipe(Effect.provideService(Clock.Clock, clock)))
console.log("clock reads by fiber:", st.reads.join(", "))
