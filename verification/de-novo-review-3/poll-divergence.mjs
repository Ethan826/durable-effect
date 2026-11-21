// The root-fiber rule (#22): Clock, Random and durable operations check Fiber.getCurrent()
// against the root. Here the forked fiber does only pure work (no clock, no random, no durable
// op), which the design lists as "Replays correctly". The root observes the child's progress
// (Ref.get / fiber.pollUnsafe) after a durable op and branches on it. The durable completion
// arrives after 40 ms live and after two setImmediate turns on replay (the N1 mechanism), so
// the root takes different branches and journals different operations. No violation is raised.
import { Clock, Effect, Random, Ref, Fiber } from "../../spike/node_modules/effect/dist/index.js"

const makeExecutor = (journal) => {
  const st = { i: 0, violations: [], root: undefined, trace: [] }
  const guard = (what) => { if (Fiber.getCurrent() !== st.root) st.violations.push(what) }
  let L = 1000
  const durable = (name, liveMs) => Effect.suspend(() => {
    guard("durable " + name)
    const idx = st.i++
    st.trace.push(name)
    return Effect.callback((resume) => {
      if (idx < journal.length) {
        if (journal[idx] !== name) st.trace.push(`JOURNAL MISMATCH: expected ${journal[idx]}`)
        setImmediate(() => setImmediate(() => resume(Effect.succeed(name))))
      } else setTimeout(() => { journal[idx] = name; resume(Effect.succeed(name)) }, liveMs)
    })
  })
  const nanos = () => { guard("clock"); return BigInt(L) * 1000000n }
  const clock = {
    currentTimeMillisUnsafe: () => { guard("clock"); return L },
    currentTimeMillis: Effect.sync(() => { guard("clock"); return L }),
    currentTimeNanosUnsafe: nanos, currentTimeNanos: Effect.sync(nanos),
    monotonicTimeNanosUnsafe: nanos, monotonicTimeNanos: Effect.sync(nanos),
    sleep: () => Effect.die("not used")
  }
  let seeded
  Effect.runSync(Effect.gen(function* () { seeded = yield* Random.Random }).pipe(Random.withSeed("inv")))
  const random = {
    nextIntUnsafe: () => { guard("random"); return seeded.nextIntUnsafe() },
    nextDoubleUnsafe: () => { guard("random"); return seeded.nextDoubleUnsafe() }
  }
  return { st, clock, random, durable }
}

// Pure work: no services touched. Effect auto-yields as it runs.
const pureWork = (progress) => Effect.forEach(Array.from({ length: 20000 }, (_, k) => k),
  (k) => Ref.update(progress, (n) => n + 1), { discard: true })

const handler = (durable) => Effect.gen(function* () {
  const progress = yield* Ref.make(0)
  const child = yield* Effect.forkChild(pureWork(progress))
  yield* durable("run fetch", 40)
  const done = yield* Ref.get(progress)
  const finished = child.pollUnsafe() !== undefined
  const r = yield* Random.next
  if (finished) yield* durable("run fast-path", 5)
  else yield* durable("run slow-path", 5)
  yield* Fiber.join(child)
  return { progressAtCompletion: done, childFinished: finished, draw: r.toFixed(3) }
})

const runAttempt = async (journal) => {
  const ex = makeExecutor(journal)
  const program = Effect.gen(function* () {
    ex.st.root = Fiber.getCurrent()
    return yield* handler(ex.durable)
  }).pipe(Effect.provideService(Clock.Clock, ex.clock), Effect.provideService(Random.Random, ex.random))
  const out = await Effect.runPromise(program)
  return { out, trace: ex.st.trace, violations: ex.st.violations }
}
const journal = []
console.log("attempt 1 (live):  ", JSON.stringify(await runAttempt(journal)))
console.log("attempt 2 (replay):", JSON.stringify(await runAttempt(journal)))
