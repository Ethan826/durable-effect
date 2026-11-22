# Deterministic scheduling dossier

Approvals: statements (revision 2), approved by the owner on 2026-11-21 (#28) / dossier, not yet approved (rule: the default of two, because AGENTS.md sets none).

This dossier defines the verification of the deterministic-scheduling design (#25, #27) and the time rule (#5) that it builds on. It follows the proof-dossier skill. The statements below are drafts for the owner's approval. No proof, model or implementation work starts on them until they are approved, and nothing built on them is adopted until the completed dossier is approved.

## Verification layers

Each statement is backed by the strongest method that can reach it. The layers, from the most abstract to the code that ships:

1. Kernel-checked proofs in Coq 8.20.1 of the core theorems about an abstract executor (S1 to S11), with each fiber modelled as an interaction tree from the Interaction Trees library (Xia et al., POPL 2020). The proof project is in `verification/proofs/`, separate from the package build, in a project-local opam switch with every version pinned. The skill's Coq gate, `check-axioms-coq.sh`, gates it: a source scan for `Admitted`, `admit`, `Axiom`, `Parameter` and `Conjecture`, a clean build, the theorem list read back from Coq, and the `Print Assumptions` report regenerated and compared. The gate's own tests pass, including a checker mutant.
2. A TLA+ model checked with TLC of the executor together with the parts of Restate and the SDK the proofs abstract away: the journal, suspension, replay, cancellation and crashes at every point. It is bounded evidence, with its grammar and bounds fixed in the file before the first run, gated like oracle 3: it exits non-zero unless every invariant holds, each mutant fails the property it names, the state counts match pinned values, and a named state is reached.
3. Environment fixtures that check each assumption the proofs make about effect 4.1.5 and the SDK (E1 to E8), against the installed packages. Each fixture asserts its result and has a mutant that makes it fail.
4. Differential tests that link the implementation to an executable reference model. The reference model is written separately from the implementation and follows the Rocq definitions. fast-check generates programs from a grammar; each program runs on the reference model and on the implementation (real Effect runtime, fake journal), across live and replay attempts with randomised arrival timing, and the traces are compared.
5. Live fixtures against a real Restate server in always-replay mode, with crashes injected at every journal index, for the cases the reviews found (F1 to F8, N1 to N6, D1 to D8) and for each statement's distinguishing example.
6. De novo reviews of the statements before approval, of the completed proofs and model, and of the model-to-implementation gap, each by an independent reviewer who decides every claim from primary evidence.

Revision 2 adds three checks the statement review found missing: fixtures that check the TLA+ model's account of the SDK against SDK 1.18.4 (the progress loops, when `run` actions execute, and which promise receives a cancellation); a review that reads the Rocq and TLA+ models side by side and records how each definition corresponds; and live fixtures for design rule 8 (actions on the default scheduler) and for the attempt-end interruption running inside a turn.

Every test and check in layers 2 to 5 follows the gate-integrity skill's standard block: it asserts its results, fails on empty input against a declared inventory, has a scan floor with a named member, and has a checker mutant and case mutants.

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

## Definitions

These are written informally here. Approval covers their meaning, and the Rocq definitions must match them. Revision 2 of the statements follows the statement review (ledger on #28).

- **D1. Fiber.** A deterministic state machine. Each step is one of: a pure step; fork a fiber, either queued (its first step is a task on the queue, as with `Effect.forkChild`) or immediate (it runs nested inside the forking step until it blocks, as concurrent `Effect.forEach` and parallel scope finalizers do); read the clock; draw a random number; start a durable operation with a kind and arguments; await a durable operation; interrupt another fiber; run a finalizer; or finish. The next step depends only on the fiber's state and the values it has received. A fiber does not observe fiber ids.
- **D2. Program.** A root fiber's initial state, together with every fiber forked from it, transitively. A program has no state shared with code outside its executor's turns (restriction R1).
- **D3. Journal.** A finite sequence of entries: a command (a durable operation's kind and arguments, or a sample request), a completion (a value or a failure for an earlier command), a cancellation, or a sample value.
- **D4. Environment.** It chooses each completion's value, each sample value, whether and when a cancellation arrives, when the attempt ends (suspension or crash), and, for the time rule, the true time and each host's clock error at every sample. In a live attempt it also chooses when each completion arrives. In a replay attempt it first supplies the journal prefix's entries in order, then behaves as in a live attempt. A mixed attempt is a replay attempt that continues live; the next attempt replays its journal.
- **D5. Executor.** One per attempt. It has one queue of tasks for all of the program's fibers, run in turns. A turn belongs to one executor and runs as one synchronous JavaScript job, with no `await` inside it, until the queue is empty. When the operation a fiber awaits has completed, the executor delivers its result at the start of the next turn: it issues the time rule's sample command inside that turn, then resumes the fiber. An abandoned operation (its fiber was interrupted) is not delivered and gets no sample, and the executor stops listening to it. The attempt-end interruption also runs as a turn. The time rule of revision 4, one seeded random stream, and the violations of #25 and #27 complete the definition.
- **D6. Trace.** The executor's externally visible actions in order: commands issued with their arguments, deliveries, clock values read, random values drawn, interruptions and finalizers run, violations, and the attempt's exit (success, failure, defect, suspension or crash).
- **D7. Arrival schedule.** In a live attempt, the points in the executor's run at which each completion arrives. Attempts with the same values may have different arrival schedules.
- **D8. Turn boundary.** A point between two turns of the same executor, at which its queue is empty.
- **D9. Replay point.** For a replay of `J[0..k)`, the longest prefix of the replay's trace that consumes only entries of `J[0..k)`.

Definitional choices to review:

- The queue's order is priority first, then queue order, as in effect 4.1.5's `MixedScheduler`. The proofs assume that order is a function of the order tasks were queued.
- At most one durable operation is awaited at a time. With more, the order of delivery would need its own statement.
- Programs are finite, but fibers may loop. Statements about a whole attempt are about every finite prefix of it.
- Cancellation is delivered to the awaited durable operation, and reported once (fixture on #20). E5b covers abandoned operations.
- `L` is an integer. Every sleep longer than 2³¹ − 1 ms is a chain of durable sleeps of at most 2³¹ − 1 ms (#24, D7), and an infinite sleep is an endless chain.

Definitional choices the Coq model added, for the dossier review (`verification/proofs/Scheduling/`):

- The attempt's end is counted in progress steps, which exclude steps that wait for an arrival. Counted in raw steps, the same point would mean different amounts of work in a live attempt and its replay, and S1 would be false for a reason unrelated to the design.
- S1 and S2 compare finite traces by prefix: any two runs are prefixes of each other. That is the dossier's choice that statements about a whole attempt are about every finite prefix.
- The sample at delivery is taken in the same step as the delivery. In the implementation it is a journaled step that must complete, but delivery happens only at an empty queue, so no other fiber can run while it is awaited, and taking it at once gives the same interleaving.
- Fibers share memory through `ReadRef` and `WriteRef`, standing for Effect's `Ref`, `Deferred` and `Queue`. Without them the model could not express review 3's D1, and S1 would hold vacuously for it.
- The attempt-end turn records an interruption of every unfinished fiber and exits; finalizers that run after the attempt has ended are not modelled, because they can issue no durable operation.
- Resumes from outside Restate are absent from D4's environment, so S1 to S4 and S6 to S11 quantify over it. S5 is stated over an extended environment that adds them.
- Revision 3's executor, needed for S9, is the same executor with two switches changed (a `Policy`), so the two cannot drift apart: revision 3 sends a sleep of up to 2⁵³ − 1 ms whole and hangs where revision 4 records a violation.

## Restrictions table

| Restriction | Why believed harmless | Challenge example |
|---|---|---|
| R1. No code outside the executor's turns writes state a handler fiber reads | Handler state is local to the invocation. Shared state across invocations is outside the guarantee, column 3 of the design. | A `run` action that updates a handler `Ref` in its closure, or a service `Ref` built once in the runtime. The statement review showed the handler reads 1 or 0 depending on timing, with no violation. |
| R2. Handler fibers keep the handler's `Scheduler` and `PreventSchedulerYield = false` | Overriding either is outside the guarantee, column 3 | With `PreventSchedulerYield` set, a step outside a turn takes effect before any violation is recorded (statement review, probe A) |
| R3. A fiber does not observe fiber ids | Ids come from one counter shared by the whole process, so they differ between attempts | `Effect.fiberId` printed in a log or used as a key |
| R4. One awaited durable operation at a time | v1 scope; more than one is #10 | `Effect.all` over two `run` steps, which v1 rejects with a defect |
| R5. Task order is a function of queue order | `MixedScheduler` drains buckets in priority then queue order (`Scheduler.ts:217-271`) | An immediate fork, which runs nested and queues nothing; D1 models it as its own kind of step |
| R6. The environment acts only through completions, samples, cancellation, attempt end and host time | Every other source is a violation or outside the guarantee | A `run` action's side effects, journaled only by their result |
| R7. Daemon and detached fibers end with the attempt | The executor and its dispatcher end with the attempt | A `forkDetach` fiber still running when the attempt suspends; the design must interrupt it |

## Statements

All are unresolved until proved or checked. Revision 2 corrects S1, S2, S3, S4, S7, S8 and S9 and adds S11.

| Id | Statement | Target label | Method | Status | Distinguishing example |
|---|---|---|---|---|---|
| S1 | Arrival independence. For any program that satisfies R1 to R3, and any two environments that supply the same completion values, sample values and cancellation, and end the attempt at the same point, the executor produces the same trace, whatever the two arrival schedules. If the attempts end at different points, the traces agree up to the earlier end. | derived | Rocq; TLC | not started | Review 3, D1: the child's progress at delivery was 20,000 live and 4,089 on replay under the old executor |
| S2 | Replay determinism. For any attempt, live, replay or mixed, with journal `J`, and any `k ≤ |J|`, a replay of `J[0..k)` produces the same trace as the original up to the replay point (D9), and every command it issues at journal index `i < k` equals `J[i]`. | derived | Rocq (from S1 and D4); TLC with crashes at every index | not started | Review 2, N2: `Effect.timeout` around pure work took different branches live and on replay |
| S3 | Violations are trace events. Whether an attempt records a violation, and where in its trace, is determined by the program and the values supplied, except for a resume not issued by this executor: from outside Restate, or from another invocation. | derived | Rocq; TLC | not started | Review 3, D2; statement review, probe C (a semaphore shared between invocations) |
| S4 | Single await. At most one durable operation is awaited at any point. A second is a violation recorded at a point fixed by S3, its command is never issued, and its action never runs. | derived | Rocq | not started | `Effect.all([run a, run b], { concurrency: 2 })` fails at the same point in every attempt, and the journal holds only `a` |
| S5 | Resumes not issued by the executor are detected. Assuming E1 and E2 and restriction R2, if a handler fiber takes a step outside a turn of its executor, the executor records a violation before that step's effect appears in the trace. | derived, relative to E1, E2 and R2 | Rocq, with E1 and E2 as hypotheses; fixtures for E1 and E2 | not started | `Effect.promise(() => fetch(...))` in a handler fails before the fetched value is used; with `PreventSchedulerYield` set, outside the guarantee |
| S6 | Blocked means blocked forever. If the queue is empty, no durable operation or sample is awaited, and the root fiber has not finished, then nothing the environment supplies resumes any fiber, so the violation never preempts a durable result. | derived | Rocq | not started | `Effect.never` fails at once; a fiber awaiting a durable sleep whose result hasn't arrived does not fail |
| S7 | Delivery. If the operation a fiber awaits has completed and its executor reaches a turn boundary, the next turn delivers that result. Every turn after the first starts with exactly one delivery or the attempt-end interruption, and nothing else. | derived | Rocq; TLC liveness under weak fairness | not started | A completion that arrives during a long turn is delivered at that turn's end; an abandoned operation's completion is never delivered |
| S8 | Time rule. `L` satisfies the time rule's claims P1 to P9 as restated in revision 4 of the design, for every arrival schedule: P9 becomes "a sleep above 2³¹ − 1 ms is a chain of durable sleeps of at most 2³¹ − 1 ms each, and an infinite sleep never completes", and P7 excludes abandoned operations. **P5 as approved is refuted**: see S8′. | derived for P2, P3, P4, P6, P8 and P9; P1 from S2; P5 and P7 under D4's host-time model | Rocq; oracle 3 kept as a regression gate after #26 | not started | Oracle 3's mutants, each of which must fail its claim |
| S8′ | P5, corrected. `L` is at most the latest sample's true time plus the largest host error, plus the server-clock lead once for every durable sleep, when true time never decreases and each timer fires at most the lead early in true time. Proposed to replace S8's P5; awaits the owner's approval. | derived | Rocq (`S8_upper`) | not started | Two 1 ms sleeps with no true time passing and a 1 ms lead: `L` is 102 against a single-lead bound of 101 (`p5_single_lead_refuted`) |
| S9 | Single-fiber equivalence. For any program with one fiber that never blocks without a durable operation awaited and never sleeps longer than 2³¹ − 1 ms, the journal and the trace under the scheduled executor equal those under revision 3's executor. Outside those conditions they differ only as follows: rule 5 turns a hang into a defect, and long sleeps become chains. | derived | Rocq (both executors defined); TLC | not started | A sequential retry loop with jitter gives the same journal under both; `Effect.never` hangs under revision 3 and fails here |
| S10 | Random replay. The sequence of random values each fiber draws is determined by the program and the values supplied. | derived, from S1 | Rocq | not started | Review 3's variant of D1 in which a branch adds or skips a draw |
| S11 | Abandonment is silent. An abandoned operation's completion, or a cancellation delivered to it, changes no trace. | derived, relative to E5b | Rocq; fixture for E5b | not started | `Effect.timeout` around pure work, whose abandoned durable timer completes later |

## Environment assumptions

The proofs treat these as hypotheses. Each one gets a fixture against the pinned packages (layer 3), with a mutant, and is checked again on every upgrade of effect or the SDK.

| Id | Assumption | Source to check | Fixture |
|---|---|---|---|
| E1 | The run loop calls `scheduler.shouldYield(fiber)` before every operation, except the first operation after an automatic yield and except when `PreventSchedulerYield` is set (R2) | `internal/effect.ts:696-707`; `Scheduler.ts:321`; `setContext` at `:803-805` | Count `shouldYield` calls against counted operations in generated programs |
| E2 | Effect's own code inside a handler never resumes a fiber from a microtask or timer it creates itself, so every resume of a handler fiber comes from a turn of its executor or a callback outside Effect | effect 4.1.5 `internal/`: the statement review found timers only in the default `ClockImpl.sleep` (replaced in handlers), the scheduler's `setImmediate` and the runtime's keep-alive interval | Run every row of the design's "replays correctly" column under the scheduled executor with a detector that fails on any step outside a turn |
| E3 | A queued fork's first step is a task on the parent's dispatcher (`internal/effect.ts:5648`), an immediate fork runs nested (`:5238`, `:4105`), and `yieldNow` queues a task (`:777`) | as cited | The statement review's `fork-immediate.mjs`, kept as a gate |
| E4 | An asynchronous `Effect.callback` resume calls `fiber.evaluate` directly, and so does an interruption triggered by an `AbortSignal` (`:5797-5803`) | `internal/effect.ts:1222-1228`, `:5797-5803` | A callback resumed from a timer and an abort, each observed outside a turn |
| E5 | The SDK reports a cancellation once, to an awaited operation, and later journaled steps succeed | Fixture on #20 | `spike/src/cancel-fixture.ts`, kept as a gate |
| E5b | When the executor stops listening to an abandoned operation, a cancellation goes to the awaited operation and not to the abandoned one. Each promise with a continuation runs its own progress loop (`promises.js:35-37, 255-264`). | SDK 1.18.4 source; unverified | A live fixture with an abandoned durable sleep and an awaited operation, cancelled through the admin API |
| E6 | On replay, the SDK resolves a journaled completion asynchronously, after the command has been issued | `restate-sdk/dist/promises.js` | A replay that records when each completion resolves |
| E7 | The SDK truncates fractional sleep durations and wraps durations of 2⁶⁴ ms or more modulo 2⁶⁴ | `restate-sdk-core/dist/duration.js`; fixture on #20 | Kept as a gate, so an SDK change is noticed |
| E8 | `Fiber.getCurrent()` reports the running fiber, including across nested inline evaluation | `internal/effect.ts:675-736`; review 3 | Nested-evaluation probe |
| E9 | A `run` action executes later, in the SDK's progress loop, not when `ctx.run` is called | `restate-sdk/dist/context_impl.js:235-300` | A trace of when the action starts relative to the handler's turn |

## Non-vacuity

Witnesses, each closed by evaluation in the kernel (`verification/proofs/Scheduling/Witnesses.v`):

- `d1_same_trace`: review 3's D1, a root that reads a cell a child writes 3,000 times (with an automatic yield) and branches on it, gives the same trace under a late live arrival and under replay.
- `d1_reads_final_value`: in that trace the branch saw the child's final value.
- `values_change_traces`: a negative control. Different sample values give different traces, so S1 does not hold because traces ignore their inputs.

Refuted, and kept:

- P5 as approved (S8). `p5_single_lead_refuted`: two 1 ms sleeps whose timers fire with no true time passing leave `L` at 102 while true time is 100, beyond the single-lead bound of 101. The corrected statement is S8′.

Two model bugs were found by running the model before any proof: it had no shared memory, so it could not express D1; and a fiber whose Coq fuel ran out at the same moment as its operation budget was stored without being queued again, so the child in D1 never finished. Both are fixed, and D1's witnesses cover both.

## Axioms report

`verification/proofs/axioms-report.txt`, regenerated by the proof-dossier skill's `check-axioms-coq.sh` from `verification/proofs/theorems.txt`. Every theorem so far is closed under the global context: no axiom, including none from Interaction Trees, which the model uses only for its core `itree` type. The gate passes: 4 modules, 4 theorems, report unchanged.

## Oracles

Oracle 3 is kept as a regression gate for the time rule once #26 gates every claim. The TLC model's grammar and bounds will be written here before its first run.

## Model-to-implementation gap

The link is differential (layer 4), with live fixtures (layer 5). The Rocq definitions are not extracted into the implementation. The differential tests compare the implementation's traces with an executable reference model that follows the Rocq definitions, on generated programs and randomised arrival schedules. A mismatch means either the implementation or the reference model is wrong, and each one found becomes a fixture. What stays unproved: that effect 4.1.5 and the SDK behave as E1 to E8 state outside the cases the fixtures run, and that the reference model matches the Rocq definitions, which a review checks by reading the two side by side.

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

## Open items

- The owner must approve S8′, which replaces S8's refuted P5, and should review the definitional choices the Coq model added.
- Revision 4 of the design must absorb the statement review's design changes: per-executor synchronous turns, the sample issued at delivery, no sample for an abandoned operation and no listener on it, R1 and R2 in column 3, immediate forks, and the end of daemon fibers with the attempt.

