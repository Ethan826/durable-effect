# Durable Effect investigation

Companion to [PLANNING.md](PLANNING.md). Start with a sequential Restate handler that uses ordinary `Effect.sleep` and `Effect.retry` with `Schedule.jittered`. Try the service overrides in `t0ster/restate-effect` first. That project already documents typed step results, durable combinators, and runtime checks on ordinary Effect concurrency over durable operations. The prototype can tell us whether replacing the default services is enough for the sequential case. [t0ster/restate-effect](https://github.com/t0ster/restate-effect#readme)

## Proposed replay contract

For a fixed deployed handler, invocation identity, input, and committed history, replay reproduces the recorded command prefix, including operation kinds, order, and arguments. Given the same subsequent recorded outcomes, it produces the same continuation and final result. An external result or clock sample that had yet to be persisted at the crash can differ when execution resumes. External writes need their own idempotency guarantees. [Restate durable steps](https://docs.restate.dev/develop/ts/durable-steps) · [Restate versioning](https://docs.restate.dev/services/versioning)

## Findings and open questions

| Finding | Status | What would settle it |
| --- | --- | --- |
| Effect exposes the needed hooks for sleep and jitter. | Source verified. Integration open. | Pin the Effect and Restate versions and show that a real invocation uses the supplied clock and random service on replay. |
| Restate and Effect can both own retries. | SDK behavior documented. Adapter policy proposed. | Verify that each expected attempt failure reaches `Effect.retry` once as a replayable typed failure, and that the SDK handles defects and interruption separately. |
| A clock refresh adds a durable step. | Source verified. Clock semantics open. | Define sampling boundaries, failure behavior, nanosecond accessors, and elapsed-time semantics. Measure the actual journal overhead. |
| Supplying a durable sleep leaves Effect's timeout race and interruption in place. | Source verified. Durable timeout deferred pending semantics. | Specify selection when both sides are ready, loser behavior, cancellation, and finalizers before implementing a timeout. |
| The type and lint restrictions have gaps. | Open. | Probe imported helpers that read wall time, services that capture the invocation context, and combinators that fork internally. Document the resulting supported subset. |
| Real-time telemetry needs separate wiring. | Effect span timing verified in source. Integration open. | Check span timestamps with the substituted clock and decide whether to wire a separate telemetry clock or defer that feature. |

### Clock and randomness

Effect's sleep delegates to the active clock. Its schedule driver reads the clock's synchronous millisecond accessor and sleeps through the clock service. Jitter draws from the active random service. Keep a seeded stream per invocation for the sequential prototype. Draws repeat when consumed in the same order. A shared stream across concurrent continuations can assign different draws to the branches when their order changes. [Effect sleep](https://github.com/Effect-TS/effect-smol/blob/main/packages/effect/src/internal/effect.ts#L5592-L5600) · [Schedule driver](https://github.com/Effect-TS/effect-smol/blob/main/packages/effect/src/Schedule.ts#L392-L409) · [Jitter implementation](https://github.com/Effect-TS/effect-smol/blob/main/packages/effect/src/Schedule.ts#L1611-L1618)

The proposed clock is sampled wall time. Reads freeze between samples, and the source clock can go backward. Decide how elapsed-time schedules and nanosecond reads behave and whether a recorded failure refreshes the clock before the retry schedule runs. Restate implements `ctx.date.now()` with `ctx.run`, so the proposed policy adds a journaled step at entry and at each refresh. Effect also uses the active clock to timestamp spans. [Restate clock implementation](https://github.com/restatedev/sdk-typescript/blob/main/packages/libs/restate-sdk/src/context_impl.ts#L110-L123) · [Effect clock interface](https://github.com/Effect-TS/effect-smol/blob/main/packages/effect/src/Clock.ts) · [Effect span timing](https://github.com/Effect-TS/effect-smol/blob/main/packages/effect/src/internal/effect.ts#L5392-L5427)

### Retry ownership and external writes

A retryable exception inside `ctx.run` can trigger SDK retries before the outer Effect sees a failure. To let Effect own backoff, have each `run` return the expected attempt outcome as a serializable value, then turn a recorded failure into a typed Effect failure outside the step. Keep real time and randomness inside the I/O boundary. The payment-hold example needs a stable idempotency key across repeats of the same external write. A crash after that write but before persistence can repeat the callback. [Restate `Context.run`](https://restatedev.github.io/sdk-typescript/interfaces/_restatedev_restate-sdk.Context#run) · [Restate durable steps](https://docs.restate.dev/develop/ts/durable-steps)

### Concurrency and API scope

In a bounded check with two ready continuations, each emitted a clock sample followed by a send. The six interleavings preserving each branch's order produced two distinct command-kind sequences: `clock, clock, send, send` and `clock, send, clock, send`. This gives a counterexample for unrestricted continuations in the model. Start with refreshes in the sequential handler, including one after any supported durable join. Consider explicit durable timeout for a Restate operation once winner selection, loser cancellation, and finalizers have defined behavior. [Effect timeout implementation](https://github.com/Effect-TS/effect-smol/blob/main/packages/effect/src/internal/effect.ts#L3446-L3495) · [Restate concurrency](https://docs.restate.dev/develop/ts/concurrent-tasks)

Ordinary Effect code preserves the intended ergonomics for the supported subset. Tagless-final can limit operations exposed by the interpreter, while TypeScript callbacks can still reach globals and captured services. Revisit that API once the prototype shows which restrictions need a stronger boundary.

## First integration spike

1. Run a sequential handler against a real Restate server with pinned versions. Use a bounded jittered retry that journals a failed attempt, sleeps, then succeeds.
2. Force replay with `alwaysReplay`. Compare operation kinds, order, arguments including timer delays, and the final result for the same invocation and recorded outcomes. Check that the retry driver sees the typed failure and that clock reads add no journal entries beyond the chosen refreshes.
3. Inject a crash after a fake external write and before its `run` result is persisted. Verify that the callback can repeat and that the external service treats the stable key as the same write.
4. Add focused cases for an immediately completed step, a recorded failure, and a clock sample that moves backward. Use the results to settle clock semantics before expanding the supported schedule surface.

The review checked upstream source and the bounded interleaving example. The live integration and crash-window checks are open. The `fdarian/effect-restate` comparison in the plan could not be verified from its primary source. Revisit P or TLA+ when defining durable race and cancellation semantics. [Restate replay testing](https://docs.restate.dev/develop/ts/testing#testing-non-determinism-bugs)
