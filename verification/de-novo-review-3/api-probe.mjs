// Runs Effect 4.1.5 APIs in a handler root fiber under a Clock and Random that apply the
// root-fiber rule (#22): every read, draw and sleep checks Fiber.getCurrent() === root.
// Reports which APIs raise violations although written as sequential code in the root.
import { Clock, DateTime, Duration, Effect, Fiber, Logger, Random, Schedule, Data } from "../../spike/node_modules/effect/dist/index.js"

const mk = () => {
  const st = { root: undefined, v: [] }
  const guard = (w) => { const f = Fiber.getCurrent(); if (f !== st.root) st.v.push(`${w}@${f ? "fiber#" + f.id : "none"}`) }
  let L = 1_000_000
  const nanos = (w) => () => { guard(w); return BigInt(L) * 1000000n }
  const clock = {
    currentTimeMillisUnsafe: () => { guard("millis"); return L },
    currentTimeMillis: Effect.sync(() => { guard("millis"); return L }),
    currentTimeNanosUnsafe: nanos("nanos"), currentTimeNanos: Effect.sync(nanos("nanos")),
    monotonicTimeNanosUnsafe: nanos("mono"), monotonicTimeNanos: Effect.sync(nanos("mono")),
    sleep: (d) => Effect.suspend(() => {
      guard("sleep")
      const ms = Duration.toMillis(d)
      if (ms <= 0) return Effect.yieldNow
      return Effect.callback((resume) => { const t = setTimeout(() => { L += Math.ceil(ms); resume(Effect.void) }, 1); return Effect.sync(() => clearTimeout(t)) })
    })
  }
  let seeded
  Effect.runSync(Effect.gen(function* () { seeded = yield* Random.Random }).pipe(Random.withSeed("inv")))
  const random = { nextIntUnsafe: () => { guard("rand"); return seeded.nextIntUnsafe() }, nextDoubleUnsafe: () => { guard("rand"); return seeded.nextDoubleUnsafe() } }
  return { st, clock, random }
}
class E extends Data.TaggedError("E") {}
const cases = {
  "Effect.sleep": Effect.sleep("10 millis"),
  "Effect.timed": Effect.timed(Effect.sleep("5 millis")),
  "DateTime.now": DateTime.now,
  "Effect.log (default logger)": Effect.log("hi"),
  "Effect.withSpan": Effect.withSpan(Effect.sleep("1 millis"), "s"),
  "Effect.fn named": Effect.fn("named")(function* () { return 1 })(),
  "retry jittered exponential": Effect.fail(new E()).pipe(Effect.retry({ schedule: Schedule.exponential("1 millis").pipe(Schedule.jittered), times: 3 }), Effect.ignore),
  "retry times": Effect.fail(new E()).pipe(Effect.retry({ times: 3 }), Effect.ignore),
  "repeat spaced recurs": Effect.void.pipe(Effect.repeat({ schedule: Schedule.spaced("2 millis"), times: 3 })),
  "repeat during": Effect.void.pipe(Effect.repeat({ schedule: Schedule.during("5 millis"), times: 50 })),
  "ensuring finalizer reads clock": Effect.void.pipe(Effect.ensuring(Clock.currentTimeMillis)),
  "acquireRelease scoped": Effect.scoped(Effect.acquireRelease(Clock.currentTimeMillis, () => Random.next)),
  "forEach sequential": Effect.forEach([1, 2], () => Effect.sleep("1 millis")),
  "forEach concurrency 1": Effect.forEach([1, 2], () => Effect.sleep("1 millis"), { concurrency: 1 }),
  "all concurrency 1": Effect.all([Effect.sleep("1 millis"), Random.next], { concurrency: 1 }),
  "Effect.cached": Effect.flatMap(Effect.cached(Random.next), (c) => c),
  "Effect.cachedWithTTL": Effect.flatMap(Effect.cachedWithTTL(Effect.void, "1 second"), (c) => c),
  "forkChild + pure + join": Effect.flatMap(Effect.forkChild(Effect.succeed(1)), Fiber.join),
  "forkChild pure with Effect.fn named": Effect.flatMap(Effect.forkChild(Effect.fn("pure")(function* () { return 2 + 2 })()), Fiber.join),
  "forkChild pure with withSpan": Effect.flatMap(Effect.forkChild(Effect.withSpan(Effect.succeed(1), "pure")), Fiber.join),
  "forkChild failing (pure)": Effect.flatMap(Effect.forkChild(Effect.fail(new E())), Fiber.join).pipe(Effect.ignore),
  "Effect.timeout pure": Effect.timeout(Effect.succeed(1), "1 second"),
  "Effect.withLogSpan + log": Effect.log("x").pipe(Effect.withLogSpan("ls")),
  "Effect.orElse/catch": Effect.fail(new E()).pipe(Effect.catch(() => Clock.currentTimeMillis)),
  "Effect.callback resumed from setTimeout then clock": Effect.callback((r) => { setTimeout(() => r(Effect.void), 1) }).pipe(Effect.andThen(Clock.currentTimeMillis)),
  "Effect.promise then clock": Effect.promise(() => new Promise((r) => setTimeout(r, 1))).pipe(Effect.andThen(Clock.currentTimeMillis)),
}
for (const [name, eff] of Object.entries(cases)) {
  const ex = mk()
  const prog = Effect.gen(function* () { ex.st.root = Fiber.getCurrent(); return yield* eff })
    .pipe(Effect.provideService(Clock.Clock, ex.clock), Effect.provideService(Random.Random, ex.random), Effect.provide(Logger.layer([])))
  const exit = await Effect.runPromiseExit(prog)
  console.log(`${name.padEnd(48)} exit=${exit._tag.padEnd(8)} violations=${ex.st.v.length ? [...new Set(ex.st.v)].join(",") : "none"}`)
}
