// Replaces Effect's default Clock and Random for one handler attempt.
//
// Clock: sampled wall time. One journaled sample at entry and one after each durable sleep; reads
// in between return the last sample with no journal entry. Clock.sleep is a durable Restate timer.
// Random: one ISAAC stream per attempt, seeded from the invocation id, so a replay repeats draws
// that are consumed in the same order.
import { Clock, Duration, Effect, Random, Schema } from "effect"
import { Restate } from "@t0ster/restate-effect"
import { record } from "./trace.ts"

const nanosPerMilli = 1_000_000n

/** Where clock samples come from. Overridable so a test can make the source go backward. */
export type SampleSource = () => number

/** One journaled clock sample, taken through Restate.run. */
const sample = (source: SampleSource) =>
  Restate.run("clock-sample", Effect.sync(source), { success: Schema.Number, error: Schema.Never })

const makeClock = (
  invocationId: string,
  invocation: Restate.InvocationApi,
  source: SampleSource,
  first: number
): Clock.Clock => {
  let wall = first
  // Monotonic time never goes back, even when the sampled source does.
  let monotonic = first
  const refresh = Effect.gen(function* () {
    wall = yield* sample(source)
    monotonic = Math.max(monotonic, wall)
    record(invocationId, { kind: "clock-refresh", wall, monotonic })
  })
  const sleepDurably = (duration: Duration.Duration) => Effect.gen(function* () {
    const millis = Duration.toMillis(duration)
    record(invocationId, { kind: "sleep", millis })
    yield* Restate.sleep(duration)
    yield* refresh
  }).pipe(Effect.provideService(Restate.Invocation, invocation))
  const readMillis = () => {
    record(invocationId, { kind: "clock-read", wall })
    return wall
  }
  return {
    currentTimeMillisUnsafe: readMillis,
    currentTimeMillis: Effect.sync(readMillis),
    currentTimeNanosUnsafe: () => BigInt(readMillis()) * nanosPerMilli,
    currentTimeNanos: Effect.sync(() => BigInt(readMillis()) * nanosPerMilli),
    monotonicTimeNanosUnsafe: () => BigInt(monotonic) * nanosPerMilli,
    monotonicTimeNanos: Effect.sync(() => BigInt(monotonic) * nanosPerMilli),
    sleep: sleepDurably
  }
}

/** Traces every draw, so replays can be compared. */
const tracedRandom = (invocationId: string, inner: Random.Random): Random.Random => ({
  nextIntUnsafe: () => {
    const value = inner.nextIntUnsafe()
    record(invocationId, { kind: "random-int", value })
    return value
  },
  nextDoubleUnsafe: () => {
    const value = inner.nextDoubleUnsafe()
    record(invocationId, { kind: "random-double", value })
    return value
  }
})

/** Runs `self` with the durable Clock and the seeded Random. */
export const withDurableServices = (source: SampleSource = Date.now) =>
  <A, E, R>(self: Effect.Effect<A, E, R>): Effect.Effect<A, E, R | Restate.Invocation> =>
    Effect.gen(function* () {
      const invocation = yield* Restate.Invocation
      const invocationId = invocation.ctx.request().id
      record(invocationId, { kind: "attempt-start" })
      const first = yield* sample(source)
      record(invocationId, { kind: "clock-refresh", wall: first, monotonic: first })
      const seeded = yield* Effect.gen(function* () { return yield* Random.Random }).pipe(Random.withSeed(invocationId))
      return yield* self.pipe(
        Effect.provideService(Clock.Clock, makeClock(invocationId, invocation, source, first)),
        Effect.provideService(Random.Random, tracedRandom(invocationId, seeded))
      )
    })
