# Deterministic scheduling dossier

Approvals:
- statements: #37 revision 9, approved by the owner on 2026-11-22. That approval covers the statements as #37 words them. The Coq forms below are the main session's rendering of them. An independent review against #37 (step 2 review, 2026-11-22) approved them with fixes, which are applied. S9 was refuted three times while proving, and by the owner's decision of 2026-11-22 it is no longer a theorem of the verification; the differences from revision 3 that refuted it are recorded under Statements;
- dossier: not yet approved. The rule is the default of two approvals, because AGENTS.md sets none.

Revision 3 of the dossier, for the model revision of #37. It replaces revision 2, whose statements were proved about a model that leaves out behaviour the design relies on (#30, findings #31 to #36). Revision 2 is kept in git history (4bbdd96); its statements and refutations are summarised under "Superseded: revision 2". Where this dossier and #37 disagree, #37 wins.

## Verification links

#37 sets five links, each established a different way:

| Link | How it is established | State |
|---|---|---|
| The theorems about the executor model, for every runtime meeting the interface | Proved in Coq | Proved: S1 to S8, S10 and S11, with `Meets concrete` and `ReleasedSampleUnreachable`; S9 refuted and dropped. Not yet reviewed as a whole |
| Effect 4.1.5 meets each interface property | Conformance tests with failing mutants, bounded evidence; checked at runtime where the interface table says so | Grammar and bounds fixed below; not started |
| The SDK and Restate behave as the executor model assumes | Live fixtures against SDK 1.18.4, bounded evidence | Listed below; not started |
| The TypeScript executor implements the Coq executor model | Differential tests against the Coq executor extracted to JavaScript, bounded evidence | The executor extracts to OCaml, and `verification/proofs/extraction/check-extraction.sh` checks it against `vm_compute` on every equality witness; the JavaScript step waits on a dependency review of js_of_ocaml, and the TypeScript executor does not exist yet |
| The real stack replays deterministically | Property tests of S1's and S2's conclusions on the real executor, Effect and a fake journal, and Restate's own replay check | Not started |

The proof project is in `verification/proofs/`, separate from the package build, in a project-local opam switch with every version pinned. The project's pinned copy of the skill's Coq gate, `verification/proofs/gate/check-axioms-coq.sh`, gates it: a source scan for `Admitted`, `admit`, `Axiom`, `Parameter`, `Conjecture` and switched-off kernel checks, a clean build, the theorem list read back from Coq, an audit of the assumptions of every constant the modules declare, and the `Print Assumptions` report regenerated and compared. Every test and check in the other links follows the gate-integrity skill's standard block: it asserts its results, fails on empty input against a declared inventory, has a scan floor with a named member, and has a checker mutant and case mutants.

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
| I4. Release at unwind | `I4`: from any reachable state, a fiber that starts a durable operation reports nothing until the await ends by a delivery, a cancellation, a defect or its own release; and no token is started twice | S4 and P3, P7, P8, P9, each through the token half only | The token half is not in #37's wording; it is what "identified by an await token" requires, and P7 is false without it. No proof uses the first half. It does not say a release follows an interruption, which the third refutation of S9 used |
| I5. Visible pending work | Not stated | none | No Coq statement depends on it. It is what makes S6's violation correct for Effect, which only the conformance suite can check |
| I6. Exit reporting | `I6`: at most one root exit report, and each one after the exit report of the first fiber registered, the root; a second report is also a violation the executor checks | none of the proved statements | The second half follows #37's "after its cleanup" and I8's "removed after it exits"; without it a runtime could leave the root registered and every verdict would be `VDefect`. "Exactly once" cannot hold over every task sequence, since a sequence may end before the root finishes |
| I7. Lifetime identities | `I7`: no identity registered twice; dependence on the state alone follows from I1 | P3, P7, P8, P9 | Relating the executor's run to `drive` needs it, because `drive` answers a registration by fiber and the executor by phase |
| I8. Fiber registry | `I8`: every entry attributed to a fiber follows its registration and none follows its exit | X6 | Registration is a question, so the executor can interrupt a fiber that registers during closing before its first step |
| I9. Finite tasks | By construction | X6, all statements about turns | `Script` is inductive, so every task returns. Whether Effect's tasks return is the conformance suite's question |

`Meets R` is the conjunction of `I1`, `I4`, `I6`, `I7` and `I8`. The properties quantify over every sequence of tasks, including sequences the executor never produces, so a runtime must also behave sensibly on those. The review of step 2 showed a trivial runtime meets `Meets`, and that the concrete runtime did not, because a second `StartRoot` restarted the root; the concrete runtime now ignores it. `Meets concrete` is proved (`rev3_meets_concrete`, Rev3Concrete.v), so the statements that assume `Meets` hold for a runtime with forks, masks, finalizers and interruption. S5, S5_exit, S6, S7 and S11 hold for every runtime, without `Meets`.

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
8. A fiber cannot unwind while the sample after its operation is pending (`step_released_sample_unreachable`). The sample is issued at a turn boundary, and nothing runs until it is applied; the proof also needs the invariant that a held cancellation never coexists with a sample a fiber waits on, since a held cancellation with a waiter is delivered before the sample. If it could, the sample would stay subscribed and be retired unapplied, with no credit, as the design's time rule says of a released operation. An earlier draft applied it and credited its chunk, which contradicted the design.
9. A release drops any delivery already queued for that await, including a 0 ms sleep's, which an earlier draft left in the queue (step 2 review, F6).
10. The trace records four things beyond what #37's trace lists, because the statements need them: `ARegister` for each fiber's first run, `AStart` for each durable start, the fiber and token each command was issued for, and `L` and the credited chunk with each applied sample. The journal is only the commands' kinds and the samples' readings.
11. A sleep of 0 ms or less issues nothing and is delivered by a queued task; it does not make its fiber the awaiter for S4.
12. A transient sample failure is an `Ended` cut.
13. The executor records only the first violation (X6). A foreign input during closing after the root's exit is a first violation and makes the verdict `VDefect`; #37 does not say this case.
14. A replay that would issue a command different from the persisted one ends at once with `VMismatch`, without closing. The comparison is Restate's: a command's kind and a run's name, but not a run's arguments or a sleep's duration (#37's link table). An earlier draft compared durations too, which would have made the differential tests demand mismatches the SDK never raises.
15. The initial sample is awaited before the root starts, so the root starts with `L` set (X2).
16. Closing drops queued deliveries, discards a held cancellation, and queues the interruption of every live fiber before any task already queued.
17. In the concrete runtime, interrupting a fiber waits for its exit, as Effect's `Fiber.interrupt` does (#34), and a cancellation or defect delivered to a fiber whose finalizer is already running ends the fiber. An earlier draft unwound the fiber into the same finalizer again, which the witness for a refused start in closing showed looping.
18. Revision 3's executor credits a whole sleep of up to 2⁵³ − 1 ms as one floor; under S9's condition no sleep is longer than one link, so the floors coincide. It records a terminal sample failure as the same violation, since both designs make it a defect.
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
| S5 | A foreign resume or interruption is recorded before any change, and the attempt exits `Defect` | `S5`, `S5_exit` | derived | proved, `step_s5`, `step_s5_exit` (StepSingle.v) | `foreign_resume_is_violation`, `foreign_interrupt_is_violation` |
| S6 | The next transition at a turn boundary, by state | `S6` | derived | proved, `step_s6` (StepSingle.v) | `blocked_root_is_violation`, `held_cancellation_reaches_waiter` |
| S7 | One cause per turn; the earliest eligible entry is handled next | `S7` | derived | proved, `step_s7` (StepSingle.v) | `cancel_during_sample_replaces_it` |
| S8 | The time rule's claims P1 to P9 | `P2` to `P9`; P1 from S2 | derived; P5 under its hypotheses | proved, `time_s8` (Time.v) | `long_sleep_is_a_chain`, `cancelled_link_credits_nothing`, `overflow_is_violation` |
| S9 | Agreement with revision 3's executor under its conditions; they differ only when the cancel signal reaches a sample | `S9`, `S9_cancel` | none | refuted in three forms (`rev3_not_s9` and others, Rev3Counter.v); dropped by the owner's decision of 2026-11-22 | `single_fiber_agrees_with_rev3`, `rev3_cancel_during_sample_is_defect`, `overflow_separates_rev3` |
| S10 | Each fiber's draws agree up to the common cut | `S10` | derived, from S1 | proved, `arrival_s10` (Arrival.v) | `values_change_traces` |
| S11 | The subscription is the latest command; a retired command's notification changes nothing; closing consumes and issues nothing | `S11` | derived | proved, `step_s11` (StepSingle.v) | `cancel_during_sample_replaces_it` (the late value 99) |

Notes on the Coq forms, for the review:

- S4's second half, S6 and S7 are stated over the step function from reachable states, since turns are not objects in the model.
- P7's second half, about the host's reading at an operation's completion, is P4 under the host's own hypothesis and has no separate Coq statement.
- P5 states the early-fire hypothesis between consecutive applied samples, for credited chunks only (#35).
- S9 is not a theorem. On programs with one fiber, this executor differs from revision 3's in five ways, each shown by a theorem closed by evaluation: a cancel signal that reaches a sample issues a replacement where revision 3 records a defect (`rev3_cancel_during_sample_is_defect`); an `L` above 2⁵³ − 1 is a violation (`overflow_separates_rev3`); after a violation the attempt closes and its finalizers run, where revision 3 stops (`rev3_clock_fin_runs`); a release reported without an interruption leaves the slot held, where revision 3 records a second operation (`rev3_spontaneous_diverges`); and a fiber still registered when the root exits makes the verdict `VDefect` (`rev3_masked_child_diverges`). Where none arises they agree (`single_fiber_agrees_with_rev3`).
- Some forms say less than #37's wording, and the proofs will not recover the difference: S7 does not say "exactly one cause" or treat cuts and foreign inputs as causes; P7 asks for some applied sample after the operation's last command, which is the operation's own only through the single subscription; S10 compares each fiber's draws by prefix, which is what "the same sequence up to the common cut" means for finite prefixes; and I4 covers "before cleanup" only for cleanup the log attributes to the fiber.

Refuted forms, kept, each machine-checked (the step 2 review's in its scratch directory; S9's in Rev3Counter.v):

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

Runs. Each property runs 1,000 programs for each of the pinned fast-check seeds 1 to 5, so 5,000 programs per property, and every mutant must fail within that budget. For I1 and I2, each program runs in three fresh Node processes and once more in a process that has already run another program from the same seed. I9's bound for a task is `MaxOpsBeforeYield` times the widest immediate fork plus one: 2,048 × 9 operations under this grammar, which allows no immediate fork inside another. Whether Effect's other combinators in the grammar fork immediately, and so nest, is to be checked against effect 4.1.5's source before the first run.

This is bounded evidence. A property that passes here holds for these programs and these journals, not for every program.

## Non-vacuity

Witnesses, each closed by evaluation in the kernel (`vm_compute`), none using an axiom:

- `Witnesses.v`, 29 theorems on the concrete runtime: the slot after a release (#31) and its live run; a held cancellation; an unobserved cancellation; a cancellation during a sample (#32) and during the initial sample; a terminal sample failure; a crash during a sample and its replay; a journal mismatch; two operations at once; a priority other than 0 (#33); a blocked root; foreign resume, foreign interruption and a resume for a token not awaited; overflow of `L`; a masked await; interruption waiting for a finalizer (#34); a cancelled root; a fork registering during closing; a start refused during closing; finalizers after a suspension; a long sleep as a chain; a cancelled link that credits nothing (#35); agreement with revision 3; and two negative controls.
- `Witnesses2.v`, 10 theorems added after the step 2 review: the stop of a closing when the next attempt starts; an `Ended` cut; a cut during closing; a foreign input during closing; a waiter that unwinds; an infinite sleep; a chain cancelled midway; a 0 ms sleep; overflow separating revision 3; and a 0 ms sleep's delivery dropped on release.
- `Rev3Counter.v`, evaluations of the five differences from revision 3 and of each S9 counterexample, on the concrete runtime and on two small runtimes that meet `Meets`.
- `Compare.v`, 8 theorems: #31, #34.1 and #34.2 on the old model (showing each finding) and on the new one, and review 3's D1 on the new model, whose old run is `d1_same_trace`.

Each witness states the expected trace or the fact it checks, and a mutated expected trace fails to compile, which was checked once by hand. When `ARegister` was added to the trace, every expected trace was recomputed, and Coq checked that each new trace with its `ARegister` entries removed equals the old one.

Not witnessed: a second root exit (`SecondExit`), which the concrete runtime never reports; and the fifth and sixth reviews' findings about a foreign-resumed continuation running during closing and its target changing the closing trace, which the model cannot express, because a foreign input never reaches the runtime (I3, by construction).

## Axioms report

`verification/proofs/axioms-report.txt`, regenerated by the project's pinned gate from `verification/proofs/theorems.txt`. Every theorem is closed under the global context: no axiom. The gate passes: 61 modules, 924 theorems, 2,157 constants audited, report unchanged. The new model's files declare no `Axiom`, `Parameter` or `Hypothesis`; the runtime is a record field of the statements, not an axiom.

## Model-to-implementation gap

Per #37's implementation link. The Coq executor model already extracts to OCaml, and `extraction/check-extraction.sh` compares it with `vm_compute` on every equality witness (34 cases, with a checker mutant and a floor); it keeps `nat` and `Z` inductive and maps only lists, pairs and strings to OCaml's. It will be compiled to JavaScript through js_of_ocaml, and fast-check will drive it and the TypeScript executor with the same streams of runtime events and exogenous inputs, comparing their whole states at every step. The JavaScript step and the differential tests do not exist yet. What the link cannot detect, and what covers it: the adapter's mapping from Effect to the interface's events (the conformance suite); how the TypeScript executor calls the SDK (the live fixtures and the end-to-end tests); process-level nondeterminism (the conformance suite's separate processes); errors in extraction itself (the extracted-against-`vm_compute` check); and sequences the generators leave out (only the end-to-end tests' determinism check).

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

What it brings in: Interaction Trees' axioms, which the `Print Assumptions` report will list for every theorem that uses them and which need the owner's approval. What it ties us to: Interaction Trees' release cycle for any move to Rocq 9, which is its own dependency review. The Kahn-network development is cited, not imported, because it targets a 2009 version of Coq.

Interaction Trees is now used only by the superseded revision 2 model in `Scheduling/`, which stays in the project so that `Compare.v` can run the earlier findings on it.

## Superseded: revision 2

Revision 2's statements S1 to S11 and S8′ were proved about the model in `verification/proofs/Scheduling/` (241 theorems at 0050227). The fourth de novo review (#30) found that model leaves out behaviour the design relies on: a pending sample (#32), the SDK's single pending subscription (#31), turn boundaries for cuts and foreign resumes (#33), Effect's interruption and exits (#34), and the forms of six statements (#35). Those theorems therefore do not count as the verification. They and the model stay in the project, unchanged, as the old side of `Compare.v`. Its two refutations stay on record: S11 before the model's fourth fix, and P5 as first approved (`p5_single_lead_refuted`), which S8′ replaced and #37's P5 keeps.

## Open items

- An independent adversarial review of the combined proofs, statements and assumptions (proof-dossier, section 7).
- The conformance suite, which needs the Effect adapter, and js_of_ocaml for the JavaScript step of the implementation link; both await the owner.
- Two behaviours of the concrete runtime that break no interface property: a fiber whose queued flag is already set is not woken by `wake`, and a fiber can resume from a `CInterrupt` continuation while blocked on another target.
- `Answers` answers a registration by fiber, while the executor answers by phase. The proofs that relate a run to `drive` handle it with I7; a reader relating a run through closing to `drive` must do the same.
- A prior-art search for correctness results stated over a runtime given only by an interface.
- The owner's review of the definitional choices, at the latest when approving the completed dossier.
