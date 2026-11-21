# durable-effect: planning

> **Status, 2026-11-21.** Planning has moved to GitHub issues. Epic #21 tracks v1, and #1 holds its design. Where this file and the issues disagree, the issues are current. In particular, durable-effect no longer builds on restate-effect (#2), and the time rule in #1 replaces the clock design below.

Revised after [INVESTIGATION.md](INVESTIGATION.md). The investigation checked the design against Effect and Restate source and found that several claims in the first draft were wrong or unproven. This version adopts its replay contract, narrows the first target to sequential handlers, and makes a live integration spike the first milestone.

## Goal

Write Restate handlers in Effect so that ordinary Effect code is replay-safe. `Effect.sleep` and `Effect.retry` with jittered schedules should become durable without the author learning a second API. `Effect.timeout` comes later, once its durable semantics are specified.

The first target is a **sequential** handler. Concurrency, durable timeout, and a stronger capability boundary wait until the prototype shows what the sequential case needs.

## Prior art

- **t0ster/restate-effect.** Handlers are Effects. Its `run` signature rejects, at compile time, actions that require Restate's invocation services, and it strips those services at runtime. It provides journaled `now` and `sleep`, and its README documents typed step results, durable combinators, and runtime checks on ordinary Effect concurrency over durable operations. Effect's default `Clock` and `Random` inside a handler are not replay-safe by default. The first spike tries replacing them through this project's service overrides before writing anything new. [README](https://github.com/t0ster/restate-effect#readme)
- **fdarian/effect-restate.** Reported to have a similar surface, an in-memory implementation for tests, and runtime-only proxies that forbid Restate services inside `run`. **Unverified:** the investigation could not confirm this from the primary source. Do not rely on it until checked.

Whether replacing the default services is enough, or whether t0ster/restate-effect already gets close, is what the spike settles. Contributing upstream remains an option once the design is proven.

## Replay contract

For a fixed deployed handler, invocation identity, input, and committed history, replay reproduces the recorded command prefix, including operation kinds, order, and arguments (timer delays included). Given the same subsequent recorded outcomes, it produces the same continuation and final result.

Outside the contract:

- An external result or clock sample that had not been persisted at the crash can differ when execution resumes.
- External writes need their own idempotency. A crash after the write but before its `run` result is persisted repeats the callback, so the caller must pass a stable idempotency key.

State each design decision below as a lemma about this contract. [Restate durable steps](https://docs.restate.dev/develop/ts/durable-steps) · [Restate versioning](https://docs.restate.dev/services/versioning)

## Design

1. **Sampled clock.** Journal wall time at invocation entry and at chosen refresh points in the sequential handler: after each durable suspension (sleep, awakeable, call, `run` completing) and after any supported durable join. `Clock.currentTimeMillis` returns the last sample with no journal entry. `Clock.sleep` is a durable Restate timer. Restate implements `ctx.date.now()` with `ctx.run`, so **each refresh is a journaled step**. The journal grows with the refresh policy as well as the author's operations; the spike measures by how much. Reads freeze between samples, and the sampled source can go backward.
2. **Seeded randomness.** Provide `Random` as one seeded stream per invocation, so jitter and generated identifiers repeat when draws are consumed in the same order. This holds for sequential code only. A shared stream across concurrent branches can hand out draws in a different order on replay.
3. **Real services inside `run`.** I/O steps get the real `Clock` and `Random`, and Restate's invocation services are excluded from their requirements at the type level. Real time and randomness stay inside the I/O boundary.
4. **Effect owns retries.** A retryable exception inside `ctx.run` triggers SDK retries before Effect sees a failure. To let `Effect.retry` own backoff, each `run` returns the expected attempt outcome as a serializable value, and the adapter turns a recorded failure into a typed Effect failure outside the step. Defects and interruption stay with the SDK.
5. **Sequential first.** In a bounded check, two ready continuations that each sample the clock and then send produced two different command sequences across their interleavings (`clock, clock, send, send` and `clock, send, clock, send`). Unrestricted concurrency with clock refreshes therefore breaks the contract. Concurrent Restate operations go through Restate's combinators, refreshes happen only after a supported durable join, and raw `Effect.fork` in a handler is out of scope for the first prototype.
6. **Timeout deferred.** Supplying a durable sleep leaves Effect's own timeout race and interruption in place, so `Effect.timeout` does not become durable for free. Before implementing a durable timeout for a Restate operation, specify which side wins when both are ready, what happens to the loser, cancellation, and finalizers.
7. **Telemetry clock.** Effect timestamps spans with the active clock, so swapping the clock also changes span timing. Either wire a separate real-time clock for telemetry or defer real-time telemetry. Decide after checking span timestamps in the spike.
8. **Globals and the supported subset.** A lint rule bans `Date`, `Math.random`, `crypto`, and timers in handler modules. Types and lint still leave gaps: imported helpers that read wall time, services that capture the invocation context, and combinators that fork internally. Probe these and document the resulting supported subset.

## API shape

Start with ordinary Effect handlers with replaced default services; this keeps the intended ergonomics for the supported subset. Tagless-final handlers can limit which operations the interpreter exposes, but TypeScript callbacks can still reach globals and captured services, so parametricity alone does not deliver the restriction. Revisit once the prototype shows which restrictions need a stronger boundary.

## Verification

- **Replay comparison.** Force replay with `alwaysReplay` and compare operation kinds, order, arguments, and final result for the same invocation and recorded outcomes. [Restate replay testing](https://docs.restate.dev/develop/ts/testing#testing-non-determinism-bugs)
- **Crash-window tests.** Crash after a fake external write and before its `run` result is persisted; check that the callback can repeat and the external service treats the stable key as one write.
- **Property-based crash-and-replay tests.** Generate sequential handlers from a small grammar (sleeps, jittered retries, runs), run each live, crash at every journal index, replay, and assert the contract. Add timeouts and joins to the grammar only once their semantics exist.
- **Model checking.** Model durable race, cancellation, and joins in P or TLA+ when defining timeout and concurrency semantics.
- **Optional formal proof.** Once the design is stable, prove that clock reads add no journal entries beyond the chosen refreshes. The first draft's lemma, that logical time adds no entries beyond the author's durable operations, is false under Restate's `ctx.run`-based clock.

## Status of the findings

| Finding | Status | What would settle it |
| --- | --- | --- |
| Effect 4 routes sleep through `Clock` and jitter through `Random`. | Verified live for the sequential subset ([spike](spike/RESULTS.md)). | Pinned versions; a real invocation uses the supplied clock and random service on replay. |
| Restate and Effect can both own retries. | Verified live: a declared `run` failure with no `retry.while` reaches `Effect.retry` once as a typed failure. Defect path not exercised. | Each expected attempt failure reaches `Effect.retry` once as a replayable typed failure; the SDK handles defects and interruption. |
| A clock refresh adds a durable step. | Verified live: reads add no entries, each refresh adds one `Run`. A max-of-samples monotonic clock under-reports elapsed time. Clock semantics open. | Sampling boundaries, failure behavior, nanosecond accessors, elapsed-time semantics, and measured overhead. |
| Durable sleep leaves Effect's timeout race in place. | Source verified. Durable timeout deferred. | Selection, loser behavior, cancellation, and finalizers specified. |
| Type and lint restrictions have gaps. | Open. | Probes of helpers, captured services, and internally forking combinators; documented subset. |
| Telemetry needs separate wiring. | Span timing verified in source. Integration open. | Span timestamps under the substituted clock. |

## Open questions

- Clock semantics: Does a recorded failure refresh the clock before the retry schedule runs? How do elapsed-time schedules and nanosecond reads behave on a frozen, possibly backward-moving clock? What happens if a refresh fails?
- Is replacing the default services through t0ster/restate-effect enough for the sequential case, or does it need a separate package?
- How much journal overhead does the refresh policy add in practice?
- How should forked fibers be prevented once concurrency is in scope: convention, a restricted type, or a runtime check?

## Milestones

1. **Integration spike** (done 2026-11-21; see [spike/RESULTS.md](spike/RESULTS.md)) (sequential, pinned Effect and Restate versions, real Restate server, t0ster/restate-effect overrides first):
   1. A handler with a bounded jittered retry that journals a failed attempt, sleeps, then succeeds.
   2. Force replay with `alwaysReplay`. Compare kinds, order, arguments including timer delays, and final result. Check that the retry driver sees the typed failure and that clock reads add no entries beyond the chosen refreshes.
   3. Crash after a fake external write, before persistence. Verify the callback repeats and the stable key deduplicates.
   4. Focused cases: an immediately completed step, a recorded failure, and a clock sample that moves backward.
2. Settle clock semantics and the telemetry clock from the spike results; document the supported subset.
3. Crash-and-replay property tests for the sequential subset.
4. P or TLA+ model of durable race, cancellation, and joins; then implement whichever timeout and concurrency semantics survive it.
5. Port the payment-hold workflow from temporal-experiment as the end-to-end example, with a stable idempotency key for the hold.
6. Decide between a standalone package and upstream contribution.
