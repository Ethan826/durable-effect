// Default logger: does Effect.log read the handler Clock in the root (allowed) and in a fork?
import { Clock, Effect, Fiber } from "../../spike/node_modules/effect/dist/index.js"
const st = { root: undefined, reads: [] }
const rd = () => { const f = Fiber.getCurrent(); st.reads.push(f === st.root ? "root" : "OTHER"); return 1 }
const clock = { currentTimeMillisUnsafe: rd, currentTimeMillis: Effect.sync(rd), currentTimeNanosUnsafe: () => BigInt(rd()), currentTimeNanos: Effect.sync(() => BigInt(rd())),
  monotonicTimeNanosUnsafe: () => BigInt(rd()), monotonicTimeNanos: Effect.sync(() => BigInt(rd())), sleep: () => Effect.void }
await Effect.runPromise(Effect.gen(function* () {
  st.root = Fiber.getCurrent()
  yield* Effect.log("root line")
  yield* Fiber.join(yield* Effect.forkChild(Effect.log("fork line")))
}).pipe(Effect.provideService(Clock.Clock, clock)))
console.log("clock reads by fiber:", st.reads.join(", "))
