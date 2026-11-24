# The standard applied to revision 6

Companion to `proposal.md`, second draft. The first draft is `derivation-v1.md`. Each component gives its claim and scope (step 1), the triggers that fire (T1 to T5, step 3), the evidence in hand, and what is open. "A" numbers are entries in the assumptions register (#48, comment 7119394545; A39 to A42 in comments 7120209653 and 7120729029; A43 in 7121147686). "F" numbers are the step 1 fixtures (comment 7119858917, `spike/rev6/order` and `spike/rev6/cancel`). "R" numbers are the run-rule fixtures (`spike/rev6/runs`, `spike/rev6/rerun`). "Precedent" names code with no stated guarantee (P6). Unless a row says otherwise, the scope is SDK 1.18.4 and server 1.8.1 with default settings, and every attempt boundary in step 1.

Under step 4, a fixture counts as evidence only once its checker has a mutant inside the claim's scope. None of the fixtures below has one yet, so each "evidence in hand" is an observation until its mutant exists. That is an open item for every row and is not repeated.

## Scheduling and delivery

### 1. Run queued work to quiescence; deliver results only between turns
- Claim: within a turn, fibers run in an order fixed by the program and the results delivered so far, and the commands issued in a turn are the same on every replay.
- T1: Effect's task order and immediate forks; Restate's progress at turn boundaries (F4 for suspension, F16 for cancellation at an await).
- T2, T3: yes. Commands issued in a different order make replay diverge, and nothing reports it before a replay.
- T4: open. It fires only if a specific determinism argument from Temporal or Durable Task is adopted, with the precondition that splitting turns into slices changes.
- Evidence: `verification/de-novo-review-4/runtime-probes-out.txt:1-8` (task priority, one fork shape).
- Open: a probe of the sliced scheduler across a slice boundary, with a control.

### 2. One race per turn over every pending durable operation
- Claim: at each turn the executor races exactly the operations that are issued and not yet delivered, minus those released, and the result it takes is the one A1 makes ready first.
- T1: A1, A2, A12 to A14, A17 to A19.
- T2, T3: yes. Racing the wrong set changes which result a turn receives, and replay diverges.
- Precedent: restate-sdk-gen, Inngest.
- Evidence: F1, F2, F5, F9 (`spike/rev6/order/run-out.txt:102-145`); A13 in `spike/abandonment/run-out-race.txt` and `run-out-gaps.txt`.
- Open: the lifecycle of released handles is row 30. A reachability argument is needed: F2 shows two sleeps already ready are won in array order, not journal order, after a wait on a subset. Either prove the executor never builds that shape, or state the tie order it gets.

### 3. Results are delivered in journal order, live and on replay
- Claim: the executor's sequence of delivered results is the same live and on replay, given A1 and A18, in every shape the executor can reach.
- T1: A1 (live in F1 and F9), A18, and A2 as the exception.
- T2: yes, over mixed operation kinds, waits on a subset, samples pending during a cancellation, and attempt cuts.
- T3: yes, as a theorem about the executor given A1 and A18 and a reachability condition that excludes A2's shape. The premises are not themselves proved.
- T4: open until the history-order argument (Burckhardt et al., OOPSLA 2021) is stated as the result we adopt.
- Evidence: F1, F9 with controls (both use runs only); F2 refutes unconditional journal-first order (`spike/rev6/order/run-out.txt:102-127,168-175`).
- Open: mixed-kind and subset-wait fixtures; a definition of which journal entries the comparison covers, including call ids, signals, samples and commands the SDK writes itself (F20 shows replay accepts changed race membership and reordered awakeables).

### 4. Several durable operations in flight from ordinary fibers
- Claim: any number of fibers may each have durable operations pending, and the journal is the same on every replay.
- T1: A13, A19, A22, A23.
- T2, T3: yes, for the reason in row 2.
- Precedent: restate-sdk-gen.
- Evidence: F5 (eight members), F8 (a child starts after the turn), F10 (closure start order varies) (`spike/rev6/order/run-out.txt:139-145,162-191`).
- Open: a fixture that drives this through Effect fibers, not hand-written races; a crash in the middle of a turn (A22).

## Cancellation and compensation

### 5. A cancellation interrupts the root fiber
- Claim: when Restate delivers a cancellation, the executor interrupts the root fiber once, at the next await, including uninterruptible regions and detached descendants as Effect defines them.
- T1: A4, A8, A38; Effect's interruption.
- T2, T3: yes. A cancellation that reaches the wrong fiber, or none, skips compensation, and nothing reports it.
- Precedent: Effect's workflow module, effect-temporal.
- Evidence: F13, F16 (`spike/rev6/cancel/run-out.txt:303-338,517-570`); the Effect probe of `Fiber.interrupt` waiting for a finalizer.
- Open: a fixture mapping a Restate cancellation to the root with uninterruptible and detached descendants.

### 6. Handler code receives at most one cancellation
- Claim: however many cancellation signals Restate delivers, handler code is interrupted once, and compensation is not interrupted.
- T1: A6, A7, A42, A43; Effect's idempotent interruption.
- T2, T3: yes. A second interruption during unwinding would restart or cut short compensation, and the undo would be lost without a report.
- T4: open. Effect documents interruption as idempotent; the trigger fires if the claim adopts that guarantee, and the note must cover Restate delivering a second signal.
- Evidence: F14, F15 (`spike/rev6/cancel/run-out.txt:371-372,438-439,471-501`); A43 shows attached children survive three cancellation requests, which is about the children, not the handler.
- Open: a fixture that sends a second cancellation during unwinding and checks the handler's finalizer trace, with a control that lets the second one through.

### 7. Compensation may start durable steps after a cancellation
- Claim: after the cancellation, compensation can issue runs, sleeps and calls, and each is journaled and completes, live and on replay.
- T1: A6.
- T2, T3: yes.
- T4: yes. The saga model (Garcia-Molina and Salem, SIGMOD 1987) assumes a compensating step eventually completes. The note must say what happens when one fails terminally.
- Evidence: F14, with plain Restate code and a control (`spike/rev6/cancel/run-out.txt:371-372,438-439`).
- Open: the same through Effect finalizers, including a compensating step that fails.

### 8. Compensation calls as one-way sends with deterministic keys, awaited through `attach`
- Claim: each compensation call is applied at most once per distinct call occurrence, across replays, repeated cancellations, crashes and kills, and two distinct occurrences never share a key.
- T1: A25, A39, A40, A43; the idempotency behaviour after cancel and kill (`spike/rev6/idem`, commit 78a158d).
- T2, T3: yes. Two occurrences sharing a key make the second alias the first (A39), so a compensation is silently skipped; a key that changes on replay applies one twice.
- T5: invented composition. Adversarial review, a fallback and the owner's approval.
- Evidence: A43 with three cancellation requests and a kill (`spike/rev6/idem/run-out-a43.txt`). Its keys come from the driver (`fixtures.mjs:408`), and its attach loop stops after four ticks (`handlers.mjs:178`).
- Open: how the executor derives a key per call occurrence (the same call site reached twice in a loop, two parent invocations, a replay); which `attach` rejections are retried and when retrying stops; a crash between sending, receiving the invocation id and attaching; any exactly-once claim qualified by Restate's retention of idempotency keys. Fixtures: same site, two parents, same key with a different payload, repeated cancellation, crash and replay, each with a control.

### 9. An interrupted fiber's child calls are cancelled
- Claim: when the executor interrupts a fiber, every call that fiber issued and that is still running is cancelled, and no other call is.
- T1: A3, A24, A33, A34.
- T2, T3: yes. A child left running performs an effect no one awaits or records.
- Precedent: Restate's agentlib `awaitChild`, effect-temporal.
- Evidence: F12 for the SDK's own cancellation on a handler cancellation (`spike/rev6/cancel/run-out.txt:76-77,145-146,228-229,276`); F13 for the 409 failure.
- Open: a fixture for the executor cancelling the calls of a fiber that lost a race, which is a different trigger from F12's.

### 10. The SDK's own cancel commands for child calls are modelled
- Claim: the model predicts the SendSignal commands the SDK journals, in position and content, in every shape the executor can reach.
- T1: A3 (live in F12), A15.
- T2, T3: yes, as a theorem about the model given A3 and A15. A model that omits them predicts the wrong journal.
- Evidence: F12; F20 mutates several fields but not SendSignal's (`spike/rev6/cancel/run-out.txt:588-690`).
- Open: a SendSignal mutation in F20.

## The clock and sleeps

Trigger 3 now covers a wrong time returned to handler code, since the executor produces it, so these rows need proofs. The owner's fallback stands: if the concurrent rule cannot be proved in time, prove it for one operation in flight and label the concurrent claims tested. The old rule is `max(l + floor, s)` (`verification/proofs/Scheduling/Model.v:183`), so the maximum alone (row 12) is only part of it.

### 11. One journaled clock sample per turn
- Claim: each turn has exactly one sample, journaled, the same on replay, including when a cancellation arrives while a sample is pending.
- T1: A27, A30.
- T2, T3: yes.
- T4: open, if Temporal's or Durable Task's one-time-per-activation guarantee is adopted.
- Evidence: `spike/RESULTS.md:18-29,34-39` for replayed sequential samples.
- Open: a sample pending during a cancellation, and a sample that fails.

### 12. The clock is the maximum of its samples
- Claim: the time returned to handler code never decreases within an invocation, across replays.
- T2, T3: yes.
- T4: yes. Hybrid logical clocks (Kulkarni et al., 2014) come with proofs; we keep only the physical part, so the note must say which results survive.
- Evidence: revision 5's proof of monotonicity in the old model (`verification/proofs/Scheduling/TimeRule.v`).
- Open: the proof restated in revision 6's model; a fixture with a sample that goes backwards.

### 13. Sleep credits when sleeps overlap
- Claim: when sleeps overlap, the clock advances by no more than the real time slept, and handler code never receives a time later than the sample bound allows.
- T1: A30, and the sample's delivery if the credit rule depends on it.
- T2, T3: yes. Two 10 ms sleeps credited in full advance the clock 20 ms, and a handler branching on a 15 ms cutoff takes the wrong branch with an exact replay.
- T5: invented. The fallback above; adversarial review; the owner's approval.
- Evidence: none for overlap. F20 checks sleep duration on replay only.
- Open: the rule's statement; a bounded check over identical, nested and partly overlapping sleeps, with replay.

### 14. Long sleeps as a chain of links
- Claim: a sleep longer than the SDK's limit is issued as a chain of links whose total equals the request, and a cancellation credits only the links completed.
- T1: A31 (code only; the in-process probe shows truncation at 1.9 ms).
- T2, T3: yes.
- T4: yes, Durable Task's timer segmentation; the note must cover A31's truncation and wraparound.
- Evidence: `verification/de-novo-review-4/runtime-probes-out.txt:28-29`; `verification/de-novo-review-3/bound-rounding-out.txt` shows three failures near the precision limit.
- Open: wraparound, negative input and a live chain with replay.

## Runs

### 15. An executed run's outcome is journaled, case by case
The first draft claimed this whenever the process survives. R5 refutes that: in its attempt 1 the process survived, Restate's abort timeout ended the attempt, and the run's result was never journaled. The claim is now split by how the attempt ends:
- Claim (a), the attempt continues: the result is journaled before the handler's output (R2).
- Claim (b), the attempt fails with a retryable error: every sibling run that had started is journaled before the attempt ends (R3s).
- Claim (c), Restate's abort timeout ends the attempt: the result may be lost; rows 23 and 24 limit the consequences.
- Claim (d), a crash or a kill: the result may be lost (A9).
- T1: A9, A11, A21, A27.
- T2, T3: yes for (a) and (b). A lost record of an executed effect is silent.
- T4: open. Temporal and DBOS record each step, but run steps outside the workflow's process, which is the precondition we lack.
- Evidence: R2 passes (`spike/rev6/runs/run-out.txt:58-65`); R3s passes, but in two cases the sibling's result was journaled after the failing run rejected (`aJournaledBeforeReject=false`), so (b) holds only as "before the attempt ends". R1 fails on delivery timing; R3 deadlocks.
- Open: the order required between a closure settling, its result being proposed, the server acknowledging it, and the attempt ending; fixtures at each of those boundaries.

### 16. An executing run stays in the race until it settles
- Claim: an executing run whose fiber was interrupted is raced in every later turn of the attempt until it settles; its result is journaled under row 15's cases.
- T1: A9; R1, R5.
- T2, T3: yes.
- T4: open, if Temporal's `WAIT_CANCELLATION_COMPLETED` guarantee is adopted.
- Evidence: F17 keeps the result when the drop control loses it; R1 keeps it but fails on delivery timing.
- Open: the inactivity-timeout case of row 15 (c).

### 17. Closing waits for executing runs
- Claim: the handler's output is journaled only after every executing run has settled and its result is journaled, while the attempt continues.
- T1: A21; R2.
- T2, T3: yes.
- T4: yes. Structured concurrency (Trio's nurseries, `asyncio.TaskGroup`) documents that a scope waits for its children; our children cannot be cancelled, and the note must say what that changes.
- Evidence: R2 with controls (`spike/rev6/runs/run-out.txt:58-65`); F7.
- Open: closing through Effect, and attempt cuts during closing.

### 18. A run's retryable failure is reported after its sibling runs settle
- Claim: a retryable failure ends the attempt only after every sibling run's closure has settled, and each sibling's result is journaled before the attempt ends.
- T1: A11; R3, R3s.
- T2, T3: yes. Reporting early loses a sibling's record, and its effect may repeat (F19).
- T4: yes. Go's `errgroup`, `asyncio.TaskGroup` and Java's `StructuredTaskScope` document waiting for siblings, but they also cancel them; we do not.
- Evidence: R3s passes; R3 (waiting for delivery) deadlocks (`spike/rev6/runs/run-out.txt:66-93`).
- Open: report "journaled by the failing attempt" separately from "journaled before the rejection" in the checker.

### 19. An interrupted run's `AbortSignal` is aborted, and a failure caused by the abort is terminal
- Claim: the executor aborts a run's signal when the run's fiber is interrupted or its deadline passes; a failure is recorded as terminal only when the abort caused it; and a terminal abort states what it implies about the external effect.
- T1: A10; the SDK passes no signal to closures; R4.
- T2, T3: yes. R4's wrapper records a terminal failure whenever the signal is aborted (`spike/rev6/runs/abort.mjs:38`). A closure that ignores the signal and then fails for an unrelated, retryable reason is recorded as terminal, though its action may never have happened or could have been retried. Nothing reports it.
- Precedent: restate-sdk-gen.
- Evidence: R4, with controls for no conversion and no abort (`spike/rev6/runs/run-out.txt:94-103`).
- Open: a causation rule for each supported API (Effect's interruption, a raw promise taking the signal), and what happens when cause is unknown; fixtures for an unrelated failure after the abort, an abort after the external write committed, and an abort at a deadline.

## Guards and closing

### 20. A handler blocked with nothing pending is a defect
- Claim (scoped per #27): when the executor's race has no members and no fiber can run, the executor records a violation; it never does so while a run is executing or a result is buffered.
- T1: A8.
- T2: yes, over the states where nothing is pending.
- T3: no. A false report stops the handler before any further effect; a missed one leaves the handler waiting until Restate's abort timeout. Neither causes trigger 3's harms.
- T5: open. #27 records the recorded violation as having no published source, while step 4 cites restate-sdk-gen's "scheduler stuck" as precedent. If the claim includes recording the violation, T5 fires.
- Evidence: F16 (`spike/rev6/cancel/run-out.txt:531-549`).
- Open: settle #27's classification; a fixture where a run is executing and the race is otherwise empty.

### 21. A resume from outside a turn is detected and refused
- Claim: any fiber resumed outside a turn is refused before it can issue a command.
- T1: Effect resumes fibers outside a turn in some cases (`verification/de-novo-review-4/runtime-probes.mjs:69-88`).
- T2, T3: yes. A missed resume lets a nondeterministic order into the journal, and nothing reports it before a replay.
- T5: invented. Approved on #27, conditionally; the fallback is Temporal-style sandboxing.
- Evidence: the probe shows resumes happen; it does not test refusal.
- Open: a refusal fixture with a control.

### 22. Fibers alive when the root exits are interrupted and their finalizers run
- Claim: when the root exits, every remaining fiber is interrupted and its finalizers run, and none of them changes the journal or performs an external effect after the root's result is decided.
- T1: Effect's interruption and finalizers; A21.
- T2: yes.
- T3: yes, if a finalizer can perform an external effect or issue a durable command after the root's result is decided, even if the executor refuses such commands, since the refusal boundary itself has to hold across replay.
- T5: open, if the claim adds an executor policy for what finalizers may do.
- Evidence: F7; the Effect probes of interruption and finalizers separately.
- Open: separate claims for ordinary exit and exit after a cancellation; a fixture with a live, detached or queued fiber that tries a durable step at exit.

## The executor rules added on 2026-11-24

### 23. Re-abort on replay
- Claim: when an attempt executes a run again, and the journal already shows the interruption or deadline that aborted it earlier, its signal is aborted before its closure starts, so the closure's work does not start.
- T1: A10 (live in F18); R5 for the narrower case where replay rebuilds the interruption before the closure starts.
- T2: yes, over any number of attempts.
- T3: yes. Without re-abort, a replay can run the work again and then succeed with one journaled result, so two executions leave one record and nothing reports it (`codex/probes.mjs`; R5's control ran the work four times with no result).
- T5: invented. The owner approved it on 2026-11-24; it needs adversarial review; the fallback is Restate's retry policy, which pauses the invocation but only after the repeats.
- Evidence: R5 (`spike/rev6/rerun/run-out.txt:18-30`).
- Open: a mutant in which the second attempt repeats the work and succeeds; the deadline case, where no lost race is replayed; the case where the first attempt's work completed its external effect before the record was lost, in which the terminal abort recorded later is wrong about the effect (row 19).

### 24. A second warning past the inactivity timeout
- Claim (scoped to one attempt): if an aborted run is still running when one inactivity timeout has passed since the attempt's last exchange with the server, the executor warns once, naming the run.
- T1: a new register entry is needed: a delivered result resets the server's inactivity timer, observed in R6's first run (`spike/rev6/rerun/run-out-1.txt`).
- T2: no for this scope. A claim across attempts and replays would trigger it.
- T5: invented. The owner approved it on 2026-11-24; it needs adversarial review; the first warning is the fallback.
- Evidence: R6 passes against its last-send control.
- Open: R6's checker accepts any time from 3500 to 7000 ms (`codex/probes.mjs`); tighten it to the deadline the claim states, and add a premature-warning mutant inside that window. The handler moves its timer only on deliveries it awaits, not on every exchange; define the warning against a condition the executor can observe locally.

## Obligations review 1 found missing

### 25. Run deadlines
- Claim: a run with a deadline has its signal aborted at that deadline, measured on a stated clock; on replay after an earlier deadline abort, row 23 applies.
- T1: A10; the clock's source.
- T2: yes. T3: yes, by row 19.
- T5: invented. Approved 2026-11-24 (comment 7132209348).
- Open: decide which clock the deadline uses and whether it may affect journal commands; fixtures for continuing after a deadline, completing exactly at it, and re-abort after it.

### 26. Kill and other attempt-ending cuts
- Claim: for each way an attempt can end (kill, crash, Restate's abort timeout, suspension, ordinary closing), the executor states what happens to sent children, executing runs and pending compensation.
- T1: A35, A36, A40, A41.
- T2, T3: yes.
- Evidence: the kill shapes in `spike/rev6/idem/run-out.txt:182-200` and `run-out-a43.txt:58-64`. Neither shows a kill undoing a completed external effect, and none is expected to.
- Open: a fixture for A35 and A36, whose harnesses were never committed.

### 27. Re-attach after a later cancellation, and later cancellation signals
- Claim: after compensation starts, a later cancellation signal reaches neither the handler (row 6) nor the attached children, and each `attach` that a cancellation rejects is attached again until the child finishes.
- T1: A4, A5, A7, A8, A24, A42, A43.
- T2, T3: yes.
- Open: when re-attaching stops, and what a child's terminal failure looks like to the handler; cancellation while a sample is pending.

### 28. The first warning
- Claim: if an aborted run has not settled within the grace period after its abort, the executor warns once, naming the run; it does not warn for a run that settled.
- T1: R4.
- T5: invented, approved 2026-11-24.
- Open: behaviour across attempts; the fields a warning must include.

### 29. SDK compatibility and the journal comparison
- Claim: the executor runs only on SDK and server versions and settings it admits (A16, A17), and refuses or reports anything else.
- T1: A15 to A18; F11 shows protocol version 7 in the fixture runs.
- T2: yes, if the claim covers how journal comparison treats each entry type.
- Open: the list of admitted versions and settings, and what happens on a mismatch.

### 30. Released handles and the wait set
- Claim: the set an executor races is defined at every turn: when an operation enters it, when release removes it, and what happens to a released operation's later result, on exit and on the next replay; an issued run that has not started is distinguished from one that is executing.
- T1: A4, A9, A10, A13, A20, A21, A23, A26, A32, A33.
- T2, T3: yes. A wrong set changes which result a turn receives (row 2).
- Open: the definition, then a bounded check of it.

### 31. Deterministic `Random`
Found missing while applying trigger 3's terms. The adapter on `main` replaces Effect's `Random` with draws from the host, one sequence per fiber (`src/adapter/Services.ts:115-138`).
- Claim: each fiber receives the same sequence of draws on every replay, whatever the interleaving of other fibers, and no handler code reads randomness any other way.
- T1: A37 (the invocation id, which can seed the draws, is the same in every attempt); the order in which Effect allocates fiber ids, since draws are keyed by fiber.
- T2, T3: yes. A draw that differs on replay is a wrong value the executor produced, and replay may then diverge or a branch may silently change.
- Precedent: Effect's seeded generator layout (effect 4.1.5 `src/Random.ts:611-627`).
- Evidence: revision 5 proves that draws agree between compatible runs (`verification/proofs/Scheduling/Determinism.v`).
- Open: the proof restated in revision 6's model, where fibers with operations in flight are created and resumed in a different pattern; a fixture comparing draws across a replay with several fibers, with a control that keys draws by something unstable.

## Documentation and tooling obligations

These were approved on 2026-11-24 (comments 7121743796 and 7132209348) and are not executor claims, so the triggers do not apply. Each still needs a check:
- runs are Effects by default, and a raw-promise run must take the signal in its type;
- the lint that flags a run that never uses its signal (#13, currently deferred) needs a planted bypass that it catches; until #13 is scheduled, revision 6 cannot count this mitigation;
- the guarantees sheet must state the actual limits of closures and transport;
- the long-work example (a separate service, a one-way send and `attach`) needs a fixture, since it is the recommended shape.

## Summary

- Proof required: 1 to 19, 21 to 23, 25 to 27, 30, 31. Rows 11 to 14 keep the owner's fallback to one operation in flight. Row 22 depends on what finalizers may do at exit.
- No proof: 20, 24, 28, 29.
- Bounded check: every row except 24 (in its one-attempt scope) and 28.
- Precedent only, so the argument comes from T2 and T3: 2, 4, 5, 9, 19, and 20 unless #27's classification changes it.
- Every fixture needs a mutant before it counts (step 4).
