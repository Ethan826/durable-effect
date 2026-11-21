// Spike handlers. Each runs under withDurableServices, so Effect.sleep, Effect.retry's schedule
// and jitter go through the durable Clock and the seeded Random.
import { Clock, Duration, Effect, Schedule, Schema } from "effect"
import { Restate } from "@t0ster/restate-effect"
import { withDurableServices } from "./durable.ts"
import { attemptCall, crashIfArmed, externalWrite } from "./external.ts"
import { record } from "./trace.ts"

export class Flaky extends Schema.TaggedError<Flaky>()("Flaky", { attempt: Schema.Number }) {}

const RetryInput = Schema.Struct({ key: Schema.String, failures: Schema.Number, times: Schema.Number })
const RetryOutput = Schema.Struct({ value: Schema.Number, finishedAt: Schema.Number })
const WriteInput = Schema.Struct({ key: Schema.String })
const WriteOutput = Schema.Struct({ idempotencyKey: Schema.String, calls: Schema.Number, applied: Schema.Number })
const BackwardInput = Schema.Struct({ samples: Schema.Array(Schema.Number) })
const BackwardOutput = Schema.Struct({ before: Schema.Number, after: Schema.Number, elapsedMillis: Schema.Number })

export const Spike = Restate.service("Spike", {
  retry: Restate.handler({ input: RetryInput, success: RetryOutput, error: Flaky }),
  write: Restate.handler({ input: WriteInput, success: WriteOutput }),
  backward: Restate.handler({ input: BackwardInput, success: BackwardOutput })
})

const invocationId = Effect.map(Restate.Invocation, invocation => invocation.ctx.request().id)

/** One attempt as a journaled step whose declared failure is final for the step, so Effect owns the retry. */
const chargeOnce = (key: string, failures: number) =>
  Restate.run("charge", Effect.suspend(() => {
    const attempt = attemptCall(key)
    return attempt <= failures ? Effect.fail(new Flaky({ attempt })) : Effect.succeed(attempt)
  }), { success: Schema.Number, error: Flaky })

const retryHandler = ({ key, failures, times }: typeof RetryInput.Type) => Effect.gen(function* () {
  const id = yield* invocationId
  const value = yield* chargeOnce(key, failures).pipe(
    Effect.tapError(error => Effect.sync(() => record(id, { kind: "typed-failure", failedCall: error.attempt }))),
    Effect.retry({ schedule: Schedule.jittered(Schedule.exponential("200 millis")), times })
  )
  const finishedAt = yield* Clock.currentTimeMillis
  return { value, finishedAt }
}).pipe(withDurableServices())

const writeHandler = ({ key }: typeof WriteInput.Type) => Effect.gen(function* () {
  const id = yield* invocationId
  // Stable across every repeat of this write: the same invocation and step.
  const idempotencyKey = `${id}:hold:${key}`
  return yield* Restate.run("hold", Effect.sync(() => {
    const result = externalWrite(idempotencyKey)
    crashIfArmed(key)
    return { idempotencyKey, ...result }
  }), { success: WriteOutput, error: Schema.Never })
}).pipe(withDurableServices())

/**
 * A source that returns the given samples in order, then repeats the last. Its position lives
 * outside the attempt (keyed by the sample list, which is unique per test invocation), because
 * every attempt calls the handler again and a per-call counter would restart.
 */
const positions = new Map<string, number>()
const scripted = (samples: ReadonlyArray<number>) => () => {
  const key = JSON.stringify(samples)
  const next = positions.get(key) ?? 0
  positions.set(key, next + 1)
  return samples[Math.min(next, samples.length - 1)] ?? 0
}

const backwardHandler = ({ samples }: typeof BackwardInput.Type) => Effect.gen(function* () {
  const before = yield* Clock.currentTimeMillis
  const [elapsed] = yield* Effect.timed(Effect.sleep("100 millis"))
  const after = yield* Clock.currentTimeMillis
  return { before, after, elapsedMillis: Duration.toMillis(elapsed) }
}).pipe(withDurableServices(scripted(samples)))

export const SpikeLive = Spike.toLayer({
  retry: retryHandler,
  write: writeHandler,
  backward: backwardHandler
}, { onDefect: "fail" })
