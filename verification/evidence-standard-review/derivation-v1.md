# The triggers applied to revision 6's components

Companion to `proposal.md`. Each component lists what each trigger requires and the evidence already in hand. T1 to T5 are the triggers in `proposal.md`. "A" numbers are entries in the assumptions register (#48, comment 7119394545); "R" numbers are the run-rule fixtures (`spike/rev6/runs/`, `spike/rev6/rerun/`). A trigger that does not fire is left out.

Rows 1 to 22 follow the step 4 table (#48, comment 7121785952), and rows 23 and 24 are the executor rules added on 2026-11-24 (comment 7132209348). In the components themselves, "run" means `ctx.run`, a closure whose result Restate journals.

## Scheduling and delivery

### 1. Run queued work to quiescence on a deterministic scheduler; deliver results only between turns.
- T1: Effect's scheduler runs queued work in a fixed order (its task priority is probed in `verification/de-novo-review-4/runtime-probes.mjs`).
- T2: yes; the claim covers every interleaving of fibers within a turn.
- T3: yes. Work done out of order issues commands in a different order, and replay then diverges. Nothing reports it until a replay.
- T4: Temporal and Durable Task document their determinism rules. Our change runs turns on Effect's scheduler and splits a turn into slices. The note must show the rules still hold across slices.

### 2. One race per turn over every pending durable operation.
- T1: A1, A2, A12, A14 and A19; A13 live (`spike/rev6`, commits 0e9ff6a and 4a140b1).
- T2: yes.
- T3: yes. The race decides which result each turn receives, so a wrong race changes the commands that follow, and replay diverges.
- T4: the only sources are code (restate-sdk-gen, Inngest), so the argument must be our own (P6).

### 3. Results are delivered in journal order, live and on replay.
- T1: A1 from the code; A18 live.
- T2: yes, as an assumption of the bounded check.
- T3: yes, as a named axiom. This is Restate's behaviour, so we prove what follows from it and do not prove the behaviour itself.

### 4. Several durable operations in flight from ordinary fibers.
- T1: A13, A19, A22, A23.
- T2: yes.
- T3: yes, for the same reason as row 2.
- T4: the only source is code (restate-sdk-gen), so the argument must be our own.

## Cancellation and compensation

### 5. A cancellation interrupts the root fiber.
- T1: A4, A8, A38; Effect's interruption.
- T2: yes.
- T3: yes. A cancellation that reaches the wrong fiber, or none, skips compensation, and nothing reports it.
- T4: the sources are code (Effect's workflow module, effect-temporal), so the argument must be our own.

### 6. Handler code receives at most one cancellation.
- T1: A6, A7; A43 live (commit 584ddd0).
- T2: yes.
- T3: yes. A second cancellation during compensation would cancel the compensation's own calls (A7), and the undo would be lost without any report. The scoring draft did not require a proof here.
- T4: Effect documents that interruption is idempotent, and Temporal documents cancellation as a state. The note must show those guarantees hold when Restate can deliver a second signal.

### 7. Compensation may start durable steps after a cancellation.
- T1: A6.
- T2: yes.
- T3: yes.
- T4: the saga model (Garcia-Molina and Salem, SIGMOD 1987) is a published argument. It assumes a compensating step can always complete eventually. The note must say what happens when a compensating step fails terminally on Restate.

### 8. Compensation calls as one-way sends with deterministic keys, awaited through `attach`.
- T1: A25; how Restate treats an idempotency key after cancel and kill (commit 78a158d, `spike/rev6/idem`); A43 live.
- T2: yes.
- T3: yes. A compensation call that is lost or runs twice is an external effect lost or duplicated.
- T5: an invented composition. It needs adversarial review, a fallback (reissue with a fresh key, exactly once only if the target is idempotent) and the owner's approval.

### 9. An interrupted fiber's child calls are cancelled.
- T1: A3, A24, A34.
- T2: yes.
- T3: yes. A child call left running performs an effect that no one awaits or records.
- T4: the sources are code (Restate's agentlib `awaitChild`, effect-temporal), so the argument must be our own.

### 10. The SDK's own cancel commands for child calls are modelled.
- T1: A3 live, A15.
- T2: yes.
- T3: yes, as named axioms. Restate's replay check compares each SendSignal field by field (A15), so a model without them predicts the wrong journals.

## The clock and sleeps

Rows 11 to 14 fall under the open question in `proposal.md`: the proof line as written does not cover the time rule. Revision 5 proves the time rule for one operation in flight.

### 11. One journaled clock sample per turn.
- T1: A27, A30.
- T2: yes.
- T3: pending the owner's decision on the time rule.
- T4: Temporal and Durable Task document one time per activation, taken from the history. The note must show that a journaled sample keeps the property they rely on, a time that is the same on every replay.

### 12. The clock is the maximum of its samples.
- T2: yes.
- T3: pending the time rule decision. Revision 5 already proves it.
- T4: hybrid logical clocks (Kulkarni et al., 2014) come with proofs. Our clock keeps only the physical part, with no logical counter, so the note must show which of their results survive.

### 13. Sleep credits when sleeps overlap.
- T1: A30.
- T2: yes.
- T3: pending the time rule decision.
- T5: invented. The registered fallback is to prove the clock for one operation in flight and label the concurrent claims tested. It still needs adversarial review and the owner's approval.

### 14. Long sleeps as a chain of links.
- T1: A31.
- T2: yes.
- T3: pending the time rule decision.
- T4: Durable Task documents timer segmentation. The note must cover A31's truncation and wraparound.

## Runs

### 15. Every executed run's outcome is journaled while the process survives.
- T1: A9, A11, A21, A27; R1 to R3.
- T2: yes.
- T3: yes. A run that executed with no record is an external effect with no record.
- T4: Temporal and DBOS document that each step is recorded, but they run steps outside the workflow's process. That precondition is the one we lack, which is why R1 shows a stall. The note must say so.

### 16. An executing run stays in the race until it settles.
- T1: A9; R1, R5.
- T2: yes.
- T3: yes, for the reason in row 15.
- T4: Temporal documents `WAIT_CANCELLATION_COMPLETED` for activities, which run on a worker and heartbeat. Ours run in the handler's process. The note must cover the inactivity timeout (R1, R6).

### 17. Closing waits for executing runs.
- T1: A21; R2.
- T2: yes.
- T3: yes.
- T4: structured concurrency (Trio's nurseries, `asyncio.TaskGroup`) documents that a scope waits for its children. Our children are external effects, which cannot be cancelled, so the note must say what that changes.

### 18. A run's retryable failure is reported after its sibling runs settle.
- T1: A11; R3 and R3s.
- T2: yes.
- T3: yes. Reporting early ends the attempt, so a sibling's record is lost and its effect may repeat (A11).
- T4: Go's `errgroup`, `asyncio.TaskGroup` and Java's `StructuredTaskScope` document waiting for siblings, but they also cancel them; we do not. R3 showed that "settled" has to mean the closure finished.

### 19. An interrupted run's `AbortSignal` is aborted, and a failure caused by the abort is terminal.
- T1: R4; the SDK passes no signal to run closures; A10.
- T2: yes.
- T3: yes. A terminal failure recorded for a run whose external call may already have happened is wrong, and nothing reports it. Revision 6 must say what a terminal abort promises about the external effect. The scoring draft rated this lower until the author overrode it.
- T4: the only source is code (restate-sdk-gen), so the argument must be our own.

## Guards and closing

### 20. A handler blocked with nothing pending is a defect.
- T1: A8.
- T2: yes. The detector must fire exactly when no progress is possible.
- T3: no. A false report fails the attempt, and a missed one leaves the handler waiting until Restate's abort timeout ends it. Both are loud.
- T4: the only source is code (restate-sdk-gen's "scheduler stuck"), so the argument must be our own.

### 21. A resume from outside a turn is detected and refused.
- T1: Effect's runtime resumes fibers outside a turn in some cases (`verification/de-novo-review-4/runtime-probes.mjs`).
- T2: yes.
- T3: yes. A missed resume lets a nondeterministic order into the journal, and nothing reports it until a replay.
- T5: invented. Approved by the owner on #27 and reviewed in earlier rounds (#30); its fallback is recorded there.

### 22. Fibers still alive when the root exits are interrupted and their finalizers run.
- T1: Effect's interruption and finalizers; A21.
- T2: yes.
- T3: yes, if a finalizer may issue a durable operation after the root's result is decided, since the journal would then depend on finalizer order. If revision 6 forbids that, a proof is not needed.
- T4: Effect documents interruption and finalizers. The note must cover finalizers that issue durable operations.

## The executor rules added on 2026-11-24

### 23. Re-abort on replay: a run that an earlier attempt aborted is aborted at once when executed again.
- T1: A10; R5 live.
- T2: yes, over any number of attempts.
- T3: no. If the rule fails, the invocation repeats the run in each attempt until Restate's retry policy pauses it, which is loud.
- T5: invented. It needs adversarial review. The fallback is that Restate's retry policy pauses the invocation. The owner approved the rule on 2026-11-24.

### 24. A second warning when an aborted run is still running once the service's inactivity timeout has passed.
- T1: R6. The timeout counts from the last exchange in either direction.
- T5: invented. It needs adversarial review. As a fallback the first warning still fires. The owner approved the rule on 2026-11-24.

## Summary

- Proof required (16 rows): 1 to 10, 15 to 19, 21. Row 22 also needs one unless revision 6 forbids durable operations in finalizers.
- Proof pending the time rule decision: 11 to 14.
- No proof: 20, 23, 24.
- Bounded check: every row except 24.
- Own argument needed, because the only source is code: 2, 4, 5, 9, 19, 20.
