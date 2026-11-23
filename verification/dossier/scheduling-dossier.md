# Deterministic scheduling dossier

Approvals:
- statements: #37 revision 9, approved by the owner on 2026-11-22. That approval covers the statements as #37 words them. The Coq forms below are the main session's rendering of them. An independent review against #37 (step 2 review, 2026-11-22) approved them with fixes, which are applied. S9 was refuted three times while proving, and by the owner's decision of 2026-11-22 it is no longer a theorem of the verification; the differences from revision 3 that refuted it are recorded under Statements;
- dossier: not yet approved. The rule is the default of two approvals, because AGENTS.md sets none.

Revision 3 of the dossier, for the model revision of #37. It replaces revision 2, whose statements were proved about a model that leaves out behaviour the design relies on (#30, findings #31 to #36). Revision 2 is kept in git history (4bbdd96); its statements and refutations are summarised under "Superseded: revision 2". Where this dossier and #37 disagree, #37 wins.

## Verification links

#37 sets five links, each established a different way:

| Link | How it is established | State |
|---|---|---|
| The theorems about the executor model, for every runtime meeting the interface | Proved in Coq | Proved: S1 to S8, S10 and S11; `Meets concrete`, `ReleasedSampleUnreachable`, `RunFromEquivalent`, `HeldStartIssuesNothing` and `HeldCancelDelivered`; S9 refuted and dropped. Reviewed as a whole, and its fixes reviewed again; both approved with fixes, which are applied |
| Effect 4.1.5 meets each interface property | Conformance tests with failing mutants, bounded evidence; checked at runtime where the interface table says so | Built and passing on 2026-11-23; bounded evidence, with the counts under "Conformance results" below |
| The SDK and Restate behave as the executor model assumes | Live fixtures against SDK 1.18.4, bounded evidence | Listed below; not started |
| The TypeScript executor implements the Coq executor model | Differential tests against the Coq executor extracted to JavaScript, bounded evidence | The executor extracts to OCaml and compiles to JavaScript through js_of_ocaml; `verification/proofs/extraction/check-extraction.sh` checks both against the kernel (see Model-to-implementation gap). The TypeScript executor does not exist yet |
| The real stack replays deterministically | Property tests of S1's and S2's conclusions on the real executor, Effect and a fake journal, and Restate's own replay check | Not started |

The proof project is in `verification/proofs/`, separate from the package build, in a project-local opam switch with every version pinned. The project's pinned copy of the skill's Coq gate, `verification/proofs/gate/check-axioms-coq.sh`, gates it: a source scan for `Admitted`, `admit`, `Axiom`, `Parameter`, `Conjecture` and switched-off kernel checks, a clean build, the theorem list read back from Coq, an audit of the assumptions of every constant the modules declare, and the `Print Assumptions` report regenerated and compared. Every test and check in the other links follows the gate-integrity skill's standard block: it asserts its results, fails on empty input against a declared inventory, has a scan floor with a named member, and has a checker mutant and case mutants. The conformance suite is the exception, and "Conformance results" lists its checkers that lack a checker mutant.

## Prior art

Searched on 2026-11-21 by a search agent, with each query recorded in its report: web searches for formal models and proofs of Temporal, Cadence, DBOS, Restate, Azure Durable Functions and Durable Task, and AWS Step Functions in TLA+, P, Coq, Lean, Isabelle and Ivy; GitHub repository and code searches for TLA+ files in the temporalio, cadence-workflow, dbos-inc, Azure, p-org and restatedev organisations; searches for proofs about deterministic multithreading and record and replay; searches for mechanized event-loop and cooperative-scheduler semantics; and searches for mechanized hybrid logical clocks. Semantic Scholar rate-limited the search after two lookups, and Springer's DOI pages require a login, so two details below are unconfirmed.

Findings:

- Burckhardt, Gillum, Justo, Kallas, McMahon, Meiklejohn, "Durable Functions: Semantics for Stateful Serverless", PACMPL 5 (OOPSLA 2021), Article 133, DOI 10.1145/3485510. A version with proofs is at https://www.microsoft.com/en-us/research/uploads/prod/2021/10/DF-Semantics-With-Proofs.pdf. It gives three lambda-calculus models of Durable Functions and paper proofs that the history model is bisimilar to the compute-storage model (Theorem 6.4), with a deterministic-replay lemma (Lemma 6.5) and record and replay lemmas (6.6, 6.7). A nearby variant of S2: determinism follows from the pure calculus, clock reads and random GUIDs are not in the formal model, and there is no statement about arrival timing. Cited for S2's structure; the differences are S1, S8 and S10.
- Kahn, "The semantics of a simple language for parallel programming", IFIP Congress 1974, with a Coq mechanization by Paulin-Mohring, "A constructive denotational semantics for Kahn networks in Coq" (2009, https://www.lri.fr/~paulin/PUBLIS/paulin07kahn.pdf). Deterministic processes with blocking reads produce outputs determined by their inputs, whatever the timing. A nearby variant of S1 for dataflow processes, not cooperative fibers with shared state. The 1974 wording is unconfirmed.
- Xia, Zakowski, He, Hur, Malecha, Pierce, Zdancewic, "Interaction Trees", POPL 2020, DOI 10.1145/3371119. A Coq library that models a program as a tree of uninterpreted external events. A modelling framework, not a proof of our claims.
- Kulkarni, Demirbas, Madappa, Avva, Leone, "Logical Physical Clocks", OPODIS 2014, LNCS 8878, DOI 10.1007/978-3-319-14472-6_2 (https://www.cse.buffalo.edu/~demirbas/publications/hlc.pdf). Cited for the `max` in the time rule. A TLA+ model by Demirbas (github.com/muratdem/HLC) is checked with TLC only and keeps physical time advancing by exactly 1, so it does not cover S8's monotonicity when samples go backward. Page numbers unconfirmed.
- Background, not the same claim: Kendo (Olszewski, Ansel, Amarasinghe, ASPLOS 2009, DOI 10.1145/1508244.1508256), DMP (Devietti, Lucia, Ceze, Oskin, ASPLOS 2009, DOI 10.1145/1508244.1508255), CoreDet (Bergan et al., ASPLOS 2010), Determinator (Aviram, Weng, Hu, Ford, OSDI 2010), LVars (Kuper and Newton, FHPC 2013; Kuper et al., POPL 2014), Abadi and Plotkin's cooperative-thread semantics (POPL 2009), and Loring, Marron and Leijen's semantics of asynchronous JavaScript (DLS 2017). None is mechanized for our claims.
- Design sources, not proofs: Temporal's TypeScript SDK (`worker-interface.ts`, `vm-shared.ts`) delivers activation jobs by resolving promises and drains microtasks before concluding; Azure Durable Task runs orchestration code on a `SynchronousTaskScheduler`. Temporal, Cadence, DBOS and Restate publish no TLA+ or P models; Restate's `restatedev/jepsen` tests its metadata store and virtual objects empirically.
- Unvetted preprints, not cited: arXiv:2608.03836 (TLA+, TLAPS and Verus models of agent checkpointing), arXiv:2611.06924, arXiv:2605.14968.

Conclusion: no published result, mechanized or on paper, states S1 for cooperative fibers with run-to-quiescence delivery, or treats journaled clock and random samples within replay. S1, S3 to S8 and S10 must be derived. S2 cites Burckhardt et al. for its structure and is derived for this executor.

The model revision of #37 adds two sources. Interaction Trees is no longer used by the new model: a task's run is a finite tree of the executor's events (`Script`), which needs no coinduction. The fiber runtime as a parameter of the proofs follows the owner's decision on #37 (third comment). The search of 2026-11-21 did not look for results stated over a runtime given only by an interface; that search is an open item.

## The runtime interface

`verification/proofs/Executor/Runtime.v`. A runtime is a state, an equivalence on states, an initial state for a program and seed, and a function that runs one task (start the root, run a queued task, deliver a result, a cancellation or a defect, request an interruption). Running a task gives a `Script`: events (start a durable operation with a token, release, queue a task with a priority, fiber exited, root exit), and questions the executor answers (clock, draw, and at a fiber's first run whether to interrupt it before its first step).

| Property | Coq form | Used by | Why this form |
|---|---|---|---|
| I1. Determinism | `I1`: the equivalence is an equivalence, and from equivalent states a task gives related scripts; S1, S2 and S10 start from any state equivalent to the initial one | S1, S2, S3, S10; the only part of `Meets` they use | A Coq runtime is a function, so equal states give equal scripts already. The equivalence makes the property the one the conformance suite tests: Effect's states in two processes are equivalent but not equal |
| I2. Closed world | By construction | All | A script reaches the outside only through its events and questions |
| I3. Guarded entry | By construction | S1, S3, S5 | A foreign resume or interruption is an input of the executor, which never passes it to the runtime |
| I4. Release at unwind | `I4`: from any reachable state, a fiber that starts a durable operation reports nothing until the await ends by a delivery, a cancellation, a defect or its own release; and no token is started twice | S4, P3, P7, P8, P9 and `HeldCancelDelivered`, each through the token half only | The token half is not in #37's wording; it is what "identified by an await token" requires, and P7 is false without it. No proof uses the first half. It does not say a release follows an interruption, which the third refutation of S9 used |
| I5. Visible pending work | Not stated | none | No Coq statement depends on it. It is what makes S6's violation correct for Effect, which only the conformance suite can check |
| I6. Exit reporting | `I6`: at most one root exit report, and each one after the exit report of the first fiber registered, the root; a second report is also a violation the executor checks | none of the proved statements | The second half follows #37's "after its cleanup" and I8's "removed after it exits"; without it a runtime could leave the root registered and every verdict would be `VDefect`. "Exactly once" cannot hold over every task sequence, since a sequence may end before the root finishes |
| I7. Lifetime identities | `I7`: no identity registered twice; dependence on the state alone follows from I1 | P3, P7, P8, P9 | Relating the executor's run to `drive` needs it, because `drive` answers a registration by fiber and the executor by phase |
| I8. Fiber registry | `I8`: every entry attributed to a fiber follows its registration and none follows its exit | none of the proved statements | Registration is a question, so the executor can interrupt a fiber that registers during closing before its first step |
| I9. Finite tasks | By construction | X6, all statements about turns | `Script` is inductive, so every task returns. Whether Effect's tasks return is the conformance suite's question |

`Meets R` is the conjunction of `I1`, `I4`, `I6`, `I7` and `I8`. The properties quantify over every sequence of tasks, including sequences the executor never produces, so a runtime must also behave sensibly on those. The proofs use them only on logs the executor produces; by the owner's decision of 2026-11-22, the conformance suite therefore also drives the Effect adapter with arbitrary generated task sequences, so that what it tests matches what `Meets` states. The review of step 2 showed a trivial runtime meets `Meets`, and that the concrete runtime did not, because a second `StartRoot` restarted the root; the concrete runtime now ignores it. `Meets concrete` is proved (`rev3_meets_concrete`, Rev3Concrete.v), so the statements that assume `Meets` hold for a runtime with forks, masks, finalizers and interruption. S5, S6, S7 and S11 are stated and hold for every runtime; S5_exit is stated with `Meets`, and its proof does not use it.

## Definitions

The executor model is `verification/proofs/Executor/Exec.v`, written as one total step function over a first-order state, beside the runtime's state and never inside it (X1 to X6). Its inputs (X1): the exogenous journal entries in the order Restate persisted them, the commands already persisted, foreign inputs placed by the executor's progress, the seeded random stream and the runtime's seed. What may differ between two attempts with the same inputs: when entries arrive, where the attempt is cut, and when a later attempt stops a closing after a cut. Revision 3's executor, for S9, is `Rev3.v`, written from revision 3's design text separately from `Exec.v`; it shares only the trace's types. The concrete runtime for the witnesses is `Concrete.v`.

Definitional choices, for the review and the dossier approval:

1. A task's script is a finite tree, so I9 holds by construction in the model.
2. I1 is stated with an equivalence on runtime states, and S1, S2 and S10 start from any state equivalent to the initial one.
3. Slices are not modelled. Foreign inputs and cuts may come between any two steps that act, which includes every point where a slice can end; the slice boundaries themselves cannot change a trace, which the review of #37 revision 9 backed with identical traces at slice sizes 1, 2,048 and unbounded.
4. Foreign inputs, cuts and the stop of a closing after a cut are placed by `progress`, the count of executor steps that acted: a task, an entry consumed, a local turn or the end of closing. A step that waits is not counted, so the placement does not depend on when entries arrive. Counted by tasks only, a cut could not fall while a sample was pending.
5. A fiber's registration is a question (`Register`) that the executor answers; during closing it answers "interrupt before the first step", as the adapter's creation hook calls `interruptUnsafe` at registration (X6.3). An earlier draft reported registration as an event, and the witness for a fork queued at the root's exit showed the fork's first step running before its interruption.
6. No await token is started twice in an attempt (I4).
7. A crash inside a task is modelled by trace prefixes: every statement compares finite prefixes, and cuts fall only between steps.
8. A fiber cannot unwind while the sample after its operation is pending (`step_released_sample_unreachable`), for every runtime: the sample is issued at a turn boundary, and nothing runs until it is applied. If a fiber could unwind then, the sample would stay subscribed and be retired unapplied, with no credit, as the design's time rule says of a released operation; an earlier draft applied it and credited its chunk, which contradicted the design. Separately, that a held cancellation coexists only with an empty subscription or the initial sample holds only under I4's token half (a runtime that starts one token twice breaks it), so the step proofs keep it in an invariant proved from I4.
9. A release drops any delivery already queued for that await, including a 0 ms sleep's, which an earlier draft left in the queue (step 2 review, F6). A dropped cancellation is held again, so that it reaches the next fiber that starts a durable operation (combined review, F1).
10. The trace records four things beyond what #37's trace lists, because the statements need them: `ARegister` for each fiber's first run, `AStart` for each durable start, the fiber and token each command was issued for, and `L` and the credited chunk with each applied sample. The journal is only the commands' kinds and the samples' readings.
11. A sleep of 0 ms or less issues nothing and is delivered by a queued task; it does not make its fiber the awaiter for S4.
12. A transient sample failure is an `Ended` cut.
13. The executor records only the first violation (X6). A foreign input during closing after the root's exit is a first violation and makes the verdict `VDefect`; #37 does not say this case.
14. A replay that would issue a command different from the persisted one ends at once with `VMismatch`, without closing. The comparison is Restate's: a command's kind and a run's name, but not a run's arguments or a sleep's duration (#37's link table). An earlier draft compared durations too, which would have made the differential tests demand mismatches the SDK never raises.
15. The initial sample is awaited before the root starts, so the root starts with `L` set (X2).
16. Closing drops queued deliveries, discards a held cancellation, and queues the interruption of every live fiber before any task already queued.
17. In the concrete runtime, interrupting a fiber waits for its exit, as Effect's `Fiber.interrupt` does (#34), and a cancellation or defect delivered to a fiber whose finalizer is already running ends the fiber. An earlier draft unwound the fiber into the same finalizer again, which the witness for a refused start in closing showed looping.
18. Revision 3's executor credits a whole sleep of up to 2⁵³ − 1 ms as one floor, where this executor credits each link; they differ for a sleep longer than one link (`rev3_differs_on_long_sleep`). It records a terminal sample failure as the same violation, since both designs make it a defect.
19. `StartRoot` after the root exists does nothing in the concrete runtime (step 2 review, F3).

## Restrictions table

| Restriction | Why believed harmless | Challenge example |
|---|---|---|
| R1. No code outside the executor's slices writes state a handler fiber reads | Handler state is local to the invocation; shared state across invocations is outside the guarantee (column 3) | A `run` action, which can now run between two slices of a turn, updating a handler `Ref`; a finalizer of an ended attempt touching a semaphore a replay waits on (#37 revision 9 review) |
| R2. Handler fibers keep the handler's `Scheduler`, `PreventSchedulerYield = false` and `MaxOpsBeforeYield` | Overriding any of them is outside the guarantee (column 3) | With `PreventSchedulerYield` set, a step outside a slice takes effect before any violation is recorded |
| R3. A fiber does not observe fiber ids, or span or trace ids | Effect draws them from a process-wide counter or `Math.random`, so they differ between attempts; lint (#13) | A handler that branches on a span id drew 1 or 2 times (#37, final review) |
| Hashing. Control flow does not depend on `HashSet` or `HashMap` iteration order, or `Equal` or `Hash` over values hashed by reference | Effect's `Hash.random` differs between processes; lint (#13) | Three processes gave three orders over `Data.TaggedError` values (#37, fifth review) |
| R4. One fiber awaits a durable operation or waits for the slot at a time | v1 scope; more is #10 | `Effect.all` of a timeout around pure work and a durable sleep |
| R5. No task priority other than 0 | A priority other than 0 is a violation, so task order is queue order | `Effect.yieldNowWith(1)` |
| R6. The environment acts only through notifications, the cancel signal, cuts and foreign inputs | Every other source is a violation or outside the guarantee | A `run` action's side effects, journaled only by their result |
| R7. A separate Effect runtime is not started inside handler code | Outside the guarantee (column 3) | A runtime started inside a turn can resume a handler fiber within it (#37, first review) |
| R8. Handler code does not run synchronous code that never returns | Outside the guarantee (column 3); I9 | A loop inside one `Effect.sync` |

## Statements

Labels and status for `verification/proofs/Executor/Statements.v`. Every proved statement is closed under the global context. The distinguishing examples are the witnesses in `Witnesses.v`, `Witnesses2.v` and `Compare.v`.

| Id | Statement (#37) | Coq | Target label | Status | Distinguishing example |
|---|---|---|---|---|---|
| S1 | Two attempts with the same inputs agree up to their common cut, whatever the arrival schedule | `S1` | derived | proved, `arrival_s1` (Arrival.v) | `released_operation_live_same`, `new_d1_live_equals_replay`; negative control `values_change_traces` |
| S2 | A replay reissues the persisted commands or fails with a mismatch, and agrees with the original up to the common cut | `S2` | derived; cites Burckhardt et al. for its structure | proved, `arrival_s2` (ArrivalReplay.v) | `crash_replay_completes`; negative control `different_journal_mismatches` |
| S3 | A violation is at the same position wherever both traces reach it | `S3` | derived | proved, `arrival_s3` (Arrival.v) | `foreign_position_matters` |
| S4 | One awaiter and one subscription; a second start is a violation with no command | `S4` | derived | proved, `step_s4` (StepAwaitTurn.v); an earlier form was refuted (see below) | `two_operations_at_once`, `unwound_waiter_is_removed` |
| S5 | A foreign resume or interruption is recorded before any change, and the attempt closes; if it exits, it exits `Defect` | `S5`, `S5_exit` | derived | proved, `step_s5`, `step_s5_exit` (StepSingle.v) | `foreign_resume_is_violation`, `foreign_interrupt_is_violation` |
| S6 | The next transition at a turn boundary, by state | `S6` | derived | proved, `step_s6` (StepSingle.v) | `blocked_root_is_violation`, `held_cancellation_reaches_waiter` |
| S7 | One cause per turn; the earliest eligible entry is handled next | `S7` | derived | proved, `step_s7` (StepSingle.v) | `cancel_during_sample_replaces_it` |
| S8 | The time rule's claims P1 to P9 | `P2` to `P9`; P1 from S2 | derived; P5 under its hypotheses | proved, `time_s8` (Time.v) | `long_sleep_is_a_chain`, `cancelled_link_credits_nothing`, `overflow_is_violation` |
| S9 | Agreement with revision 3's executor under its conditions; they differ only when the cancel signal reaches a sample | `S9`, `S9_cancel` | none | refuted in three forms (`rev3_not_s9` and others, Rev3Counter.v); dropped by the owner's decision of 2026-11-22 | `single_fiber_agrees_with_rev3`, `rev3_cancel_during_sample_is_defect`, `overflow_separates_rev3` |
| S10 | Each fiber's draws agree up to the common cut | `S10` | derived, from S1 | proved, `arrival_s10` (Arrival.v) | `values_change_traces` |
| X5 | A held cancellation reaches the next fiber that starts a durable operation, before any durable command is issued; a start that receives it issues no command | `HeldCancelDeliveredFirst` (the order X5 states), `HeldCancelDelivered` (a weaker form, also proved), `HeldStartIssuesNothing` | derived | proved, `step_held_cancel_delivered_first` (StepHeldOrder.v), `step_held_cancel_delivered` (StepHeldRun.v), `step_held_start_issues_nothing` (StepHeld.v); an earlier form was refuted (see below) | `held_cancel_survives_release`, `finalizer_absorbs_held_cancel`, `closing_drops_queued_cancel` |
| Equivalent starts | A run from any state equivalent to the initial one reaches the same executor state at every step, so the statements about traces (S8) and about executor states (S4, X5) hold in any process | `RunFromEquivalentState`, and `RunFromEquivalent` for traces | derived | proved, `arrival_run_from_state` and `arrival_s4_from_equivalent` (ArrivalRunFromState.v), `arrival_run_from_equivalent` (ArrivalRunFrom.v) | none needed |
| S11 | The subscription is the latest command; a retired command's notification changes nothing; closing consumes and issues nothing | `S11` | derived | proved, `step_s11` (StepSingle.v) | `cancel_during_sample_replaces_it` (the late value 99) |

Notes on the Coq forms, for the review:

- S4's second half, S6 and S7 are stated over the step function from reachable states, since turns are not objects in the model.
- P7's second half, about the host's reading at an operation's completion, is P4 under the host's own hypothesis and has no separate Coq statement.
- P5 states the early-fire hypothesis between consecutive applied samples, for credited chunks only (#35).
- S9 is not a theorem, and the list below is not a claim that the two executors agree anywhere else. With one fiber, this executor differs from revision 3's in at least these ways, each shown by a theorem closed by evaluation: a cancel signal that reaches a sample issues a replacement where revision 3 records a defect (`rev3_cancel_during_sample_is_defect`, Witnesses.v); an `L` above 2⁵³ − 1 is a violation (`overflow_separates_rev3`, Witnesses2.v); after a violation the attempt closes and its finalizers run, where revision 3 stops (`rev3_clock_fin_runs`, Rev3Counter.v); a release reported without an interruption leaves the slot held, where revision 3 records a second operation (`rev3_spontaneous_diverges`, Rev3Counter.v); a sleep longer than 2³¹ − 1 ms is a chain of links where revision 3 sends one command (`rev3_differs_on_long_sleep`, Witnesses4.v); and a task priority other than 0 is a violation where revision 3 runs it (`rev3_differs_on_priority`). A blocked root is a violation where revision 3 hangs (`rev3_differs_on_blocked_root`), and an infinite sleep is an endless chain where revision 3 sends nothing (`rev3_differs_on_infinite_sleep`); in these two revision 3's trace is a prefix of this one's. With two fibers there is one more: a fiber still registered when the root exits makes the verdict `VDefect` (`rev3_masked_child_diverges`, Rev3Counter.v). Revision 3's executor models no cuts, replay or foreign inputs. The two traces are equal on the program of `single_fiber_agrees_with_rev3`.
- Some forms say less than #37's wording, and the proofs will not recover the difference: S7 does not say "exactly one cause" or treat cuts and foreign inputs as causes; P7 asks for some applied sample after the operation's last command, which is the operation's own only through the single subscription; S10 compares each fiber's draws by prefix, which is what "the same sequence up to the common cut" means for finite prefixes; and I4 covers "before cleanup" only for cleanup the log attributes to the fiber.

Refuted forms, kept, each machine-checked (the step 2 review's in its scratch directory; S9's in Rev3Counter.v):

- `HeldCancelDelivered` without `Meets`: a runtime that starts one token twice makes the executor issue a command while the held cancellation waits in the queue (`step_held_cancel_delivered_refuted`, against `HeldCancelDeliveredFirstForm`). The form with `Meets` is proved (`step_held_cancel_delivered`).

- S9 and S9_cancel as first written. A trivial runtime that meets `Meets` refutes both: a cut, a persisted journal that differs, a terminal sample failure and an initial sample of 2⁵³ + 3 each separate the two executors (`S9_false`, `S9_cancel_false`).
- S9 and S9_cancel in their second form, with "one fiber" read from the registry between steps: a child that registers during closing, after the root has left the registry, separates them (`rev3_not_s9_second_form`).
- S9 and S9_cancel in their third form, with registrations counted: closing after a violation runs a finalizer revision 3 never runs (`rev3_not_s9`), and a release with no interruption leaves the slot held (`rev3_not_s9_without_violation`).
- S4 as first written. Its second clause quantified over every state, and a state with an awaiter and an earlier violation recorded no `SecondOp` (`S4_false`); its first clause lacked `Meets`, and a runtime that reused a token broke it (`S4_clause1_false_without_Meets`).

## The SDK side: live fixtures

The environment assumptions of revision 2 map onto the interface and the fixtures. E1 and E4 now fall under I3, E2 under I2, E3 under I5 and E8 under I8, and the conformance suite tests them. E5b is refuted (#31) and replaced by the executor-owned subscription. E5, E6, E7 and E9 stay as SDK fixtures. #37 lists the live fixtures against SDK 1.18.4, each with a mutant that must make it fail:

- a released operation held while a second fiber waits for the slot, across suspension and replay, with no error-driven retries;
- a cancel signal while a released operation holds the slot, delivered to the waiting fiber with its command never issued;
- a cancel signal with nothing subscribed, reaching the next command's wait;
- the negative control: a subscription abandoned without the slot, which must fail;
- the journal of a cancellation during a sample, with the late notification; a cancellation during the initial sample;
- a terminal and a transient sample failure; a crash during a sample; callbacks after closing;
- a handler ending with a released `run` step that never executes;
- the earliest eligible entry winning at a turn boundary, live and on replay;
- a forced suspension; a forced suspension during a long turn of pure work; a finalizer that runs in the closing after a suspension; a busy handler ended by Restate's abort timeout; and an uninterruptible finalizer loop whose closing stops when the next attempt starts.

## The conformance suite: grammar and bounds

Fixed here before the first run (#37). The suite generates programs with fast-check from the combinators in the design's "replays correctly" column, runs each under the executor's dispatcher, clock and random services with a scripted journal, and checks each interface property. Every property has the mutants #37 names, each a runtime adapter that breaks it and must make its test fail.

Grammar. A program is a root fiber and up to three forked fibers. Each fiber's body is a sequence of one to six statements drawn from:

- a durable `run` step of one of three kinds; a durable sleep of 0, 1 or 5 ms;
- a `Clock` read; a `Random` draw;
- `Effect.yieldNow`;
- a loop of N steps with N in {1, 2, 2,049, 5,000}, so that a loop crosses `MaxOpsBeforeYield`;
- `Effect.repeat` or `Effect.retry` with a zero-delay schedule of N steps, N as above;
- `Effect.timeout` around pure work, with a 1 or 5 ms timeout, and the pure work a loop as above;
- `Effect.race` of two pure loops, and of a durable operation against a pure loop;
- `Effect.fail` and `Effect.die`, caught or uncaught;
- `Effect.retry` and `Effect.repeat` with a 1 ms `spaced` schedule, plain or `jittered`, of up to three steps;
- `Effect.timed`, `DateTime.now`, a log line, and `Effect.fn` with a span;
- a call to another handler; `Effect.never`; and two fibers each awaiting a deferred the other completes, a deadlock;
- `Effect.all` over pure work and at most one durable operation, with concurrency 2 or unbounded;
- `Effect.forEach` with concurrency unbounded over 1 to 8 elements, each a loop as above, not nested inside another immediate fork;
- `Effect.cached` around a loop;
- `Ref.update` and `Ref.get` on one of two shared refs; `Deferred.succeed` and `Deferred.await` on one of two shared deferreds; `Queue.offer` and `Queue.take` on one shared queue;
- `Effect.forkChild` or `Effect.forkDetach` of another fiber's body; `Fiber.join`, `Fiber.interrupt` and `Fiber.poll` on a forked fiber;
- `Effect.uninterruptible` around a sub-sequence; `Effect.ensuring` and `Effect.acquireRelease` with a finalizer that is a sub-sequence of up to two statements, and may yield.

Nesting depth is at most three.

Journals. Each program runs against scripted journals in which every notification's value is drawn from {0, 1, 2}, and the cancel signal is absent or placed before any one of the first four notifications. Foreign resumes and interruptions are generated separately, for I3's tests.

For I1, after each program ends, the test runs three further tasks from each final state, a queued task, a delivery and an interruption request, and their logs must match too, so that a private bit set early and read late is caught.

Runs. Each property runs 1,000 programs for each of the pinned fast-check seeds 1 to 5, so 5,000 programs per property, and every mutant must fail within that budget. For I1 and I2, each program runs in three fresh Node processes and once more in a process that has already run another program from the same seed.

I9's bounds, as the owner approved them on 2026-11-23. B is `MaxOpsBeforeYield`, 2,048. An operation is one increment of a fiber's `currentOpCount`; line numbers are in effect 4.1.5's `internal/effect.ts` unless another file is named.

- Per run loop, the main check: no run loop passes B + 1 = 2,049 operations. Read in the source: `currentOpCount` changes only when a fiber is made (:528), when a loop starts (:685), before each scheduler check (:693) and in `succeedWith` (:765), which returns to the loop at every multiple of 32 (`maxInlineSteps`, :843). 2,048 is such a multiple, so the check comes by the 2,049th operation. Measured: the adapter's largest loop is 2,048 in every program run. The `neverYields` mutant fails this check; its 2,049-step loops ended at 2,052 to 2,059, so a limit of 2,080 would miss some.
- Restrictions, argued from the source: a program supplies no `Scheduler` and no `PreventSchedulerYield` of its own, and writes no fiber field; the adapter registers each fiber at its first operation, with an empty stack. A program with its own scheduler ran 5,017 operations in one loop (measured). A fiber that first meets the adapter's scheduler with frames on its stack keeps `yielding` set after a registration interrupt (:698-723). The suite counts such fibers and requires none, and a fixture shows the count catches one.
- The work behind one counted operation: unchecked. Outside the grammar it is unbounded; measured, a generator that yields 100,000 values counted 19 operations. Inside the grammar no check bounds it. The constructs that loop within one operation do so over at most 8 elements (`forEach`, `all`), two sides (`race`), the waiters of one deferred or the takers of one queue, but no test measures this.
- Per task, a ceiling checked on every run: (B + d)(S·W + K·L) + 2·W·K·L·t = 3,790,848 operations, with d = 32, K = 4 fibers that run statements, D = 2 deferreds, W = 8 elements of the widest immediate fork, L = 384 statements per body and t = 8 (measured). S = max(K, 3) + D(K − 1) + K(K − 1)/2 + 2K = 24 counts the run loops of statement fibers in one task:
  - entry run loops, max(K, 3): loops a task starts itself, through the dispatcher (`src/adapter/Scheduler.ts:44-52`), `evaluate` (:619-637) and an interrupt of a fiber not running (:612). One queued task can start several: the queue's release task resumes takers until its messages run out (`Queue.ts:2519-2531`). Unresolved: the derivation gives no argument for max(K, 3), and the review tallied 23 to 24 in all; only the S oracle backs it.
  - deferred wakes, D(K − 1): each deferred completes once and resumes every waiter inline (`Deferred.ts:1697-1710`, :1226), at most K − 1 of them (argued).
  - exit wakes, K(K − 1)/2: a fiber's exit runs its observers inline (:661), which resumes a join; a body joins only bodies after it (argued).
  - interrupt run loops, K: interrupting a fiber that is not running evaluates it inline (:594-618), at most once per statement fiber in a task (argued).
  - interruptChildren run loops, K: a fiber with children runs one more loop after its own ends (:644-648), once per statement fiber (argued).

  A queue taker wakes in a task of its own, never inside the offering fiber's task. The grammar's queue is unbounded (`conformance/interpret.ts:231`, capacity infinite at `Queue.ts:491`), so an offer appends the message and asks for a release (`Queue.ts:851-852`), which goes through the dispatcher (`Queue.ts:2533-2542`) and which the adapter queues as a separate host task (`src/adapter/Scheduler.ts:45-49`). The taker's loop starts at the top of that task, so the entry term covers it (read in the source). An oracle that shares no code with the operation counter counts statement-fiber run loops in each task and requires at most 24, over the suite's programs and the pinned cases (measured: at most 7, in chain2).
- Pinned cases, which the suite always runs: two forks woken inline by one deferred, each running a concurrent `forEach` of 8 (32,784 operations in one task), and chain2, in which every body runs races whose large side loses between wakes (3,014,585). Each meets the per-run-loop bound, the ceiling and the S check, and each must exceed 18,432 in one task (measured).

The first bound, 2,048 × 9 per task, was refuted. A deferred resumes its waiters inside the task that completes it (:1226), so one task can run several forks' slices, and a race whose large side loses runs a full slice inline while its parent continues (:1749-1801). Each of the pinned cases exceeds it.

This is bounded evidence. A property that passes here holds for these programs and these journals, not for every program.

### Conformance results

`bun run conformance` ran the whole suite on Node 26.6.0 on 2026-11-23: 161 tests, all passing, in 13 minutes 48 seconds. These counts come from that run's output. They are bounded evidence: each property held for these programs, seeds and journals.

| Property | Result | Counts |
|---|---|---|
| I1, I2, I7, I9 | pass | 5,000 programs each (seeds 1 to 5, 1,000 per seed), 20,000 runs reported; most operations in one task 14,371, in one run loop 2,048; most statement-fiber loops in a task 5. 10 mutants (`randomChoice`, `privateBit`, `timeoutResume`, `timerCell`, `capturedTimer`, `hashSetOrder`, `processCounter`, `sameIdentity`, `reuseExited`, `neverYields`) each fail their property |
| I3, I4, I5, I6, I8 | pass | 5,000 programs each; 14 mutants each fail their property. The floors held, for example 1,898 masked waiters resumed, 2,034 unmasked and 30,094 masked interrupts of awaits, 112,666 idle tasks, 1,294 success, 193 failure and 2,035 interrupted root exits, 10,100 fibers, 66 registered while closing |
| I4, I6, I7, I8 over arbitrary task sequences | pass | 5,000 sequences; 10,840 second starts, 46,255 stray deliveries, 10,018 stale interrupts, 2,407 awaits and 3,718 root exits; the check of each property catches one mutant |

The suite fails on an empty grammar inventory (38 statement kinds, 1,000 samples), and a full scan must reach program 999 of seed 5 in the determinism and lifecycle runs and sequence 5,000 (seed 5's last) in the sequence run. Each of I1, I2, I7 and I9 must compare 5,000 programs, and the lifecycle and sequence runs must cover 5,000 each. `conformance/listing.check.ts` fails when a check file is in no script or a script names a missing file. `conformance/gate.check.ts` turns off one comparison at a time in a scratch copy of the I1, I2, I7 and I9 checkers, the determinism, lifecycle and sequence scan floors, the comparison floor, the sequence scan's note of the required sequence, the inventory check and the file-list check, and the fixtures must fail on a named test each time.

Checkers without a checker mutant: the lifecycle `scanMinimums` floors and `shortfall`, the sequence `unusualFloors` and `shortOf`, the grammar's other tests (loop counts, nesting, widths, journal values), and the log-property checks in `logprops.ts`. The two floor sets have a fixture that shows a low count is named. The log-property checks each have a fixture that breaks only one clause, and the sequence run catches an adapter mutant for each.

Pinned I9 cases, always run: two forks woken inline by one deferred, each running a `forEach` of 8, ran 32,784 operations in one task (4 statement-fiber loops); chain2 ran 3,014,585 (7 statement-fiber loops). Each ran at most 2,048 operations in one run loop and exceeded 18,432 in one task.

Grammar gap: `Fork` has no masked-start option (`conformance/grammar.ts:59`), and 5,000 programs registered no fiber that Effect had masked during closing. #37's two I8 closing cases, an uninterruptible detached fork and a concurrent `forEach` in a closing finalizer, are therefore covered only by the pinned cases in `conformance/closing.ts`. In each, a masked fiber registers during closing, I6, I8 and the log properties hold, and the I8 mutant that leaves that fiber out fails.

The resume guard in `src/adapter/Scheduler.ts` (commit 27e06e2) was added in Task 12. The owner had approved detecting a foreign resume through `shouldYield` on #27, but no earlier task had built it. I3's tests needed it.

## Non-vacuity

Witnesses, each closed by evaluation in the kernel (`vm_compute`), none using an axiom:

- `Witnesses.v`, 29 theorems on the concrete runtime: the slot after a release (#31) and its live run; a held cancellation; an unobserved cancellation; a cancellation during a sample (#32) and during the initial sample; a terminal sample failure; a crash during a sample and its replay; a journal mismatch; two operations at once; a priority other than 0 (#33); a blocked root; foreign resume, foreign interruption and a resume for a token not awaited; overflow of `L`; a masked await; interruption waiting for a finalizer (#34); a cancelled root; a fork registering during closing; a start refused during closing; finalizers after a suspension; a long sleep as a chain; a cancelled link that credits nothing (#35); agreement with revision 3; and two negative controls.
- `Witnesses2.v`, 10 theorems added after the step 2 review: the stop of a closing when the next attempt starts; an `Ended` cut; a cut during closing; a foreign input during closing; a waiter that unwinds; an infinite sleep; a chain cancelled midway; a 0 ms sleep; overflow separating revision 3; and a 0 ms sleep's delivery dropped on release.
- `Rev3Counter.v`, evaluations of three differences from revision 3 and of each S9 counterexample, on the concrete runtime and on two small runtimes that meet `Meets`.
- `Witnesses3.v`, 1 theorem added after the combined review: a held cancellation that survives the release of the fiber it was queued for (F1).
- `Witnesses4.v`, 6 theorems added after the second review: four differences from revision 3 (a chained sleep, a priority, a blocked root, an infinite sleep), and two cancellations that conform to X5 and X6 while the invocation succeeds (a released child's finalizer receives the held cancellation; closing drops a queued one).
- `Compare.v`, 8 theorems: #31, #34.1 and #34.2 on the old model (showing each finding) and on the new one, and review 3's D1 on the new model, whose old run is `d1_same_trace`.

Each witness states the expected trace or the fact it checks, and a mutated expected trace fails to compile, which was checked once by hand. When `ARegister` was added to the trace, every expected trace was recomputed, and Coq checked that each new trace with its `ARegister` entries removed equals the old one.

Not witnessed: a second root exit (`SecondExit`), which the concrete runtime never reports; and the fifth and sixth reviews' findings about a foreign-resumed continuation running during closing and its target changing the closing trace, which the model cannot express, because a foreign input never reaches the runtime (I3, by construction).

## Axioms report

`verification/proofs/axioms-report.txt`, regenerated by the project's pinned gate from `verification/proofs/theorems.txt`. Every theorem is closed under the global context: no axiom. The gate passes: 69 modules, 1,029 theorems, every one closed under the global context. The new model's files declare no `Axiom`, `Parameter` or `Hypothesis`; the runtime is a record field of the statements, not an axiom.

## Model-to-implementation gap

Per #37's implementation link. The Coq executor model extracts to OCaml and is compiled both natively and to JavaScript through js_of_ocaml. `extraction/check-extraction.sh` takes every trace equality in the witness files and in Rev3Counter.v, splitting conjunctions of any length, and compares the extracted executor's trace with the one the kernel checked, natively and under Node: 57 cases agree in both, and the script fails unless exactly 57 do, so coverage cannot shrink silently. Two more cases compare one extracted run with another (run = run, run = run3), so they are counted apart, as self-comparisons. Statements that are not trace equalities are skipped and printed by name, and Compare.v's old-model traces are not covered. A checker mutant fails in both targets. The extraction keeps `nat` and `Z` inductive and maps only lists, pairs and strings to OCaml's; under Node it needs a stack of 8,000 frames, because inductive constants such as the concrete runtime's fuel nest deeply. fast-check will drive the JavaScript executor and the TypeScript executor with the same streams of runtime events and exogenous inputs, comparing their whole states at every step. The differential tests do not exist yet. What the link cannot detect, and what covers it: the adapter's mapping from Effect to the interface's events (the conformance suite); how the TypeScript executor calls the SDK (the live fixtures and the end-to-end tests); process-level nondeterminism (the conformance suite's separate processes); errors in extraction itself (the extracted-against-`vm_compute` check); and sequences the generators leave out (only the end-to-end tests' determinism check).

## Proof toolchain

The owner chose Coq with Interaction Trees on 2026-11-21, provided the toolchain installed cleanly and the gate ported. The proof project uses a project-local opam switch, with exact versions frozen in `verification/proofs/opam-switch.lock`.

| Package | Version | Why this version |
|---|---|---|
| coq | 8.20.1 | The newest version Interaction Trees' CI tests (8.14 to 8.20). Interaction Trees 5.2.1 does not compile on Rocq 9.3, which changed how `fun` binders parse. |
| coq-itree | 5.2.1 | The latest release. MIT licence; maintained, last pushed 2026-11-02; the library from Xia et al., POPL 2020. |
| coq-paco | 4.2.3 | Required by Interaction Trees for coinductive proofs |
| coq-ext-lib | 0.13.2 | Required by Interaction Trees |
| dune | 3.23.1 | Interaction Trees' build file uses dune's Coq extension, which dune 3.24 removed |
| ocaml-base-compiler | 5.3.0 | The compiler for the switch |
| js_of_ocaml-compiler | 6.5.0 | The latest release, for OCaml 4.13 to 5.6; added by the owner's decision of 2026-11-22 (see below) |

What it brings in: Interaction Trees' axioms, which the `Print Assumptions` report will list for every theorem that uses them and which need the owner's approval. What it ties us to: Interaction Trees' release cycle for any move to Rocq 9, which is its own dependency review. The Kahn-network development is cited, not imported, because it targets a 2009 version of Coq.

Review record for js_of_ocaml-compiler, added on 2026-11-22:

- Why: #37's implementation link runs the extracted Coq executor in the same process as fast-check and the TypeScript executor, so that one generated stream drives both step by step. Nothing in the switch compiles OCaml to JavaScript.
- Alternatives considered: running the natively compiled extraction as a subprocess from the TypeScript tests, which adds no package but needs a serialization protocol between the two, a new hand-written component in the trusted path. Melange and wasm_of_ocaml also compile OCaml for JavaScript runtimes; they were not evaluated, because #37 names js_of_ocaml and it met the need. The subprocess lost to running the very definitions the theorems are about in the tests' own process, with no protocol in between.
- Footprint: 15 opam packages in the proof switch only (cmdliner, gen, menhir and its libraries, ocaml-compiler-libs, ppx_derivers, ppxlib, sedlex, seq, sexplib0, yojson). Nothing ships in the package.
- Fit: used only by `extraction/check-extraction.sh` and, later, the differential tests.
- Release cycle and maintenance: maintained by the Ocsigen team; the opam repository holds versions 3.7.1 to 6.5.0. The pin moves only with a review.
- Security and supply chain: built from source by opam, with checksums frozen in `opam-switch.lock`; no install scripts beyond the OCaml build.
- License: the compiler is GPL-2.0-or-later and its runtime LGPL-2.1-or-later with the OCaml linking exception. The project uses the compiler as a tool and ships none of its output, so the GPL places no condition on the package.
- Pinning: exact, 6.5.0, frozen with the rest of the switch by `opam switch export --full --freeze`.

Interaction Trees is now used only by the superseded revision 2 model in `Scheduling/`, which stays in the project so that `Compare.v` can run the earlier findings on it.

## Superseded: revision 2

Revision 2's statements S1 to S11 and S8′ were proved about the model in `verification/proofs/Scheduling/` (241 theorems at 0050227). The fourth de novo review (#30) found that model leaves out behaviour the design relies on: a pending sample (#32), the SDK's single pending subscription (#31), turn boundaries for cuts and foreign resumes (#33), Effect's interruption and exits (#34), and the forms of six statements (#35). Those theorems therefore do not count as the verification. They and the model stay in the project, unchanged, as the old side of `Compare.v`. Its two refutations stay on record: S11 before the model's fourth fix, and P5 as first approved (`p5_single_lead_refuted`), which S8′ replaced and #37's P5 keeps.

## Open items

- For the owner: a held cancellation can be absorbed by a released fiber's finalizer, or dropped when closing starts, and the invocation can then succeed (`finalizer_absorbs_held_cancel`, `closing_drops_queued_cancel`). Both follow X5 and X6.1 as written; whether the root should always see a cancellation is a question for the spec.
- P8's second half still assumes that no command is issued between a start and its cancellation; `HeldStartIssuesNothing` and `HeldCancelDeliveredFirst` cover the start step and every durable command, not sample commands. Proving P8's second half without the hypothesis is open.
- The conformance suite, which needs the Effect adapter, and js_of_ocaml for the JavaScript step of the implementation link; both await the owner.
- Two behaviours of the concrete runtime that break no interface property: a fiber whose queued flag is already set is not woken by `wake`, and a fiber can resume from a `CInterrupt` continuation while blocked on another target.
- `Answers` answers a registration by fiber, while the executor answers by phase. The proofs that relate a run to `drive` handle it with I7; a reader relating a run through closing to `drive` must do the same.
- A prior-art search for correctness results stated over a runtime given only by an interface.
- The owner's review of the definitional choices, at the latest when approving the completed dossier.
