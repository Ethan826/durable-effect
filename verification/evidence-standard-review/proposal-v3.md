# Proposal: the evidence each component of revision 6 must have

Third draft, 2026-11-24, revised after two independent reviews (`codex/report.md`, `codex/report-2.md`). Not yet approved. Once the review is settled, this goes to #48 as the step 4 standard. Earlier drafts are kept as `proposal-v1.md` and `proposal-v2.md`, and the sections "What changed after review 1" and "What changed after review 2" map each finding to its change.

## Where this fits

durable-effect runs Effect v4 handlers on Restate so that they are replay-safe. Design revision 6 (#48) moves the executor to one race per turn over every pending durable operation. Step 4 of #48 is a provenance table: each component of revision 6 with its closest published source, its fidelity (faithful, adapted or invented) and the standard alternative. The draft table is comment 7121785952 on #48.

The table says where each component comes from. It does not say what evidence each component needs before revision 6 can rely on it. The project rules (`AGENTS.md`) set a floor for the whole project. Anything that decides, orders or guarantees something needs an oracle or property test that shares no logic with the implementation, and a provenance entry. No statement may depend on a Restate or SDK behaviour until a live fixture with a failing control has checked it. The target is a proved and tested v1 by 2026-12-13, so the proof effort has to go where it matters. This proposal sets the per-component requirement.

## A scoring scheme, considered and rejected

An earlier draft scored each component on three ordinal axes (importance, novelty, risk) and added the scores. The owner rejected it: nothing makes one step on one axis equal to one step on another, and the clamps and floors it needed showed that the author's judgement, not the arithmetic, was deciding.

## The proposal

### Step 1: state each claim with its scope

The triggers apply to claims, not to component names, and the same component can need different evidence depending on what it claims. Review 1 showed this with the second warning: read as a timer rule within one attempt, it needs no bounded check; read as a guarantee across an attempt boundary and a replay, it does. So each component is first written as one or more claims in observable terms, each with its scope:

- what an observer outside the executor can see when the claim holds or fails: journal entries, external effects, values returned to handler code, warnings;
- the programs it covers: which operations, how many fibers, whether finalizers may issue durable operations;
- the attempt boundaries it covers: success, suspension, an attempt ended by Restate's abort timeout, a crash, a kill, and the replays that follow;
- the SDK and server versions and settings it assumes.

A claim with no stated scope cannot be checked against the triggers and goes back to its author.

### Step 2: what each kind of evidence establishes

| Evidence | What it establishes | What it assumes |
|---|---|---|
| A register entry and a fixture with a failing control: live against a Restate server, or an in-process probe for the Effect runtime | That the external system behaved as stated in the shapes the fixture ran, at the pinned versions | That the shapes run cover the claim's scope, and that the checker rejects wrong answers inside that scope |
| A bounded exhaustive check that shares no logic with the executor (step 7 of #48) | That no counterexample exists within the stated grammar and bounds | That the grammar can express every behaviour in the claim's scope; a grammar without pending samples cannot find a bug that involves one |
| A mechanised Coq proof with no `admit`, its axioms reported by the prover, a non-vacuity check, and differential tests that tie the extracted executor to the TypeScript one | That the claim holds for every input the model can express, given the stated premises | That the model expresses the approved behaviour, and that each premise is backed by a register entry |
| An adaptation note | That each precondition of a borrowed argument still holds after our change | That the source's argument is sound |
| Adversarial review, a recorded fallback and the owner's approval | That an independent reader looked for a false statement and reported what was found, and that there is a way back if one is found later | The reviewer's diligence. It is aimed directly at wrong claims and definitions, though an independently stated oracle can also expose one, as #35's witnesses did |

The first draft claimed that each kind catches an error all the others miss, and the second that one kind can never stand in for another. Both reviews found overlaps: a bounded check and a live fixture can both catch a replay comparison that ignores a call's payload, and an exhaustive check and a proof can establish the same property of the same finite model. So the standard makes no claim of exclusivity. Each trigger names the evidence that answers the question that trigger raises, and the standard requires that evidence even where another kind might happen to cover the same ground. The project has seen two cases where the kind of evidence it had could not have caught the error that occurred. The fourth de novo review (#30) found proofs that held for a model that left out behaviour the design relied on. R6's first run refuted a belief about Restate's inactivity timer that a proof would have taken as an axiom.

### Step 3: the triggers

Each claim is checked against five triggers. The claim's requirement is the union of what it triggers. No weighting is involved. The triggers apply to the executor's decisions; behaviour of Restate, the SDK or Effect that a claim relies on is covered by trigger 1 alone.

1. If the claim depends on how the Restate server, the SDK or the Effect runtime behaves, each such premise needs a register entry and a fixture with a failing control for the claim's scope. In proofs the premise is a named axiom. The premise itself is not proved, and a register entry never satisfies trigger 3.
2. If the claim quantifies over interleavings, attempts, replays or journal contents, it needs the bounded exhaustive check. The grammar, bounds and exclusions are published before the check runs, and its result reports coverage of each boundary the claim's scope names.
3. A claim about an executor decision needs a proof if a violation could go undetected until after one of these has happened: an external effect is performed twice, performed when it should not be, or skipped; a journal record is lost; replay diverges; or handler code receives a wrong value from the executor. A value counts here if the executor produces or selects it: which result reaches which await, how a failure is classified (terminal or retryable, a cancellation or an ordinary failure), and the times, keys and random draws it generates. The test is whether the value could differ if the executor were wrong while Restate behaved as the register says. A payload the executor passes through unchanged from the journal (a run's result, a call's response, an awakeable's value) does not count; its evidence comes from trigger 1 and a round-trip test of the codec. Detection is judged at the first violation, and only two observers count: the executor, through a check that runs before the action it guards, and Restate, through a journal mismatch that stops the attempt before its next command. Detection counts only if it prevents the harm. A report that lets the action go ahead does not count, and neither does a failure reported after the harm, such as Restate's retry policy pausing an invocation that has already repeated an external call. When the claim rests on premises from trigger 1, the proof is a theorem about the executor given those premises.
4. If the claim adopts a source's argument (a paper or a specification that states a guarantee and supports it) and our change touches that argument's preconditions, it needs an adaptation note. The trigger fires only when an argument is actually adopted. Code with no stated guarantee is precedent: it shows that a design has been used, and the row records it as precedent, but it supplies no argument. The argument must then come from triggers 2 and 3 where they fire, and otherwise from the property test or oracle that the project floor requires.
5. If no source has the component, it needs adversarial review, a recorded fallback and the owner's approval. "No source" means none in the prior-art search recorded on #48 (comment 7119246326) or in a search recorded in the row itself, where a source counts only if it makes the same observable claim in a comparable scope. A row that cites a near match states why it is not the same.

Trigger 3 is the only judgement about consequences, and the owner sets its terms once, not per component. The approach follows assurance standards such as DO-178C, which set a software level from the severity of a failure condition and attach a list of specific objectives to each level, rather than computing a score.

### Step 4: when a fixture discharges a claim

This is a policy about discharge, not about what a fixture shows. A fixture's output is an observation of what happened in the shapes it ran, whatever its checker. It discharges a claim's trigger 1 obligation only if its checker has been shown to reject a wrong answer inside the claim's scope: a mutant, or an existing control that changes the answer while keeping the shape. F9 already has one: its control swaps two winners in a saved trace, and `codex/probes-2.mjs` shows its main predicate also rejects two swapped winners in a real replay log. R6 does not: review 1 found that its checker accepts any warning time from 3.5 s to 7 s, including one 3 s before the deadline it is meant to confirm, because its control showed only that a different policy fails. One mutant does not show that a checker rejects every wrong answer; it shows the checker is not blind to the one the claim most needs. Probes of a checker, such as `codex/probes.mjs`, are kept beside the fixture and rerun with it.

## Applied to revision 6

`derivation.md` applies these steps to 32 components: the 22 rows of the step 4 table, the two executor rules added on 2026-11-24, six obligations review 1 found missing, the deterministic `Random`, and the outcome the executor reports, which review 2 found missing. For each it states the claim and its scope, the triggers that fire, the evidence in hand, and what is still open.

## Claims this proposal makes

- P1: Each trigger names the kind of evidence that answers the question it raises. (Earlier versions claimed the kinds were exclusive; both reviews refuted that.)
- P2: Once a claim and its scope are written down as in step 1, and the search domain for trigger 5 is recorded, triggers 1, 2, 4 and 5 can be decided from the claim and its cited sources without judging consequences.
- P3: Trigger 3 requires a proof exactly for the executor decisions where a violation could cause one of its listed harms before the executor or Restate detects it in a way that prevents the harm.
- P4: Every requirement in `derivation.md` follows from the triggers, and no trigger that fires is left out.
- P5: `derivation.md` covers every component and approved obligation of revision 6 decided so far.
- P6: Code with no stated guarantee supplies no argument, so a component whose only source is code gets its argument from triggers 2 and 3 where they fire, and otherwise from the project floor's property test or oracle.
- P7: Under step 4's policy, a fixture discharges a claim's trigger 1 obligation only if its checker rejects a wrong answer inside the claim's scope.

## Known weaknesses

- The owner set trigger 3's value terms on 2026-11-24, in this session; the ruling is recorded on #48 when this standard is posted there, and has no durable record until then. Applying trigger 3 still takes judgement about when a violation is detected, and each row records that judgement so it can be challenged.
- No bounded check grammar exists yet. Until one is published, every T2 in `derivation.md` is an obligation with no means of discharge.
- The evidence is only as good as the gates that run it. The fourth review found an axioms gate that passed a module-level hypothesis of `False` (#30); #36 fixed it, and the gate's tests now include that mutant (`verification/proofs/gate/test-check-axioms-coq.sh:101-113`). Revision 6's proofs will name new premises, and the gate needs a check that every axiom it reports is on an allowed list tied to register entries.
- Documented guarantees of the Effect runtime are still treated as premises that need probes. That costs probes, but the fourth review found a finalizer whose timing differed from the model's (#34).
- Many rows now list open obligations that need new fixtures. The standard says what is missing; it does not supply it, and 2026-12-13 may not leave time for all of it.

## What changed after review 1

| Finding in `codex/report.md` | Checked against | Change |
|---|---|---|
| P1 unsupported: the kinds of evidence overlap | The report's example of a payload-blind comparison | P1 weakened to different assumptions; the step 2 table states them |
| P2 fails: a claim's scope decides its triggers (rows 20, 24) | Rows 20 and 24 of `derivation-v1.md` state no scope | Step 1: claims are stated with their scope first |
| P3 fails: without re-abort, a replay can repeat work and then succeed with one record | R5's control (4 executions, no result) and `codex/probes.mjs`, rerun here | Trigger 3 judged at the first violation; row 23 needs a proof |
| P3: a handler branching on a time can act wrongly with no replay divergence | The time rule's purpose (comment 7121677014) | Trigger 3 covers every value the executor produces or selects for handler code (owner's decision, 2026-11-24); rows 11 to 14 need proofs, and row 31 was added |
| P4 fails: axioms counted as proofs, and T4 used to record "no argument" | Rows 3 and 10, and rows 2, 4, 5, 9, 19 and 20, of `derivation-v1.md` | Trigger 1 premises never satisfy trigger 3; precedent recorded apart from trigger 4 |
| P5 fails: deadlines, kill, re-attach, first warning, SDK compatibility, released handles and approved mitigations have no rows | Comments 7120209653, 7121743796 and 7132209348 | Rows 25 to 30 and a list of documentation obligations |
| Finding 1: rows 15 and 16 claim more than R5 allows | R5 attempt 1: the process survived, the attempt ended, and no record was written (`spike/rev6/rerun/run-out.txt`) | Rows 15 and 16 restated case by case; the unconditional claim dropped |
| Finding 2: A43 does not establish compensation identity | `spike/rev6/idem/fixtures.mjs:408` passes the keys from the driver; the attach loop stops after 4 ticks (`handlers.mjs:178`) | Row 8 lists identity, re-attach and crash fixtures as open |
| Finding 3: journal order needs a reachability argument | F2 in `spike/rev6/order/run-out.txt` | Rows 2 and 3 state the reachability obligation |
| Finding 4: terminal conversion misses an unrelated failure after the abort | `spike/rev6/runs/abort.mjs:38` tests only `convert && controller.signal.aborted` | Row 19 lists a causation rule and its fixtures as open |
| Finding 5: claims need scope, coverage and acceptance criteria | As above | Steps 1 and 4; trigger 2's published grammar |
| Finding 6: R6's checker accepts a wide window | `codex/probes.mjs`, rerun here: 3,501 warning times from 3500 to 7000 ms accepted | Step 4; row 24 lists a tighter checker and its mutant as open |
| Finding 7: the time decision is wider than stated | `verification/proofs/Scheduling/Model.v:183`: the old rule is `max(l + floor, s)` | Rows 11 to 14 separate the maximum from end-to-end timing |

## What changed after review 2

| Finding in `codex/report-2.md` | Checked against | Change |
|---|---|---|
| P1 fails: two kinds can establish the same property | The report's finite-model example | Exclusivity dropped; P1 says each trigger names the evidence for its question |
| P2 fails: trigger 5's negative cannot be decided from the cited sources | Row 20: #27 calls the recorded violation invented, while comment 7121785952 cites a stuck detector | Trigger 5 now names its search domain and what counts as the same source |
| P3 fails: the observers who count were unclear, and reporting was treated as detection | Rows 20 and 29 of `derivation-v2.md` | Trigger 3 names the executor and Restate, and counts detection only if it prevents the harm; it applies to executor decisions |
| P4 fails: rows 24, 25, 28 and 29 omit triggers that fire | `derivation-v2.md` | Rows corrected |
| P5 fails: the reported outcome, warning advice and timeout settings are missing | Comments 7120209653 and 7132209348; the #34 probe ends a cancelled root as `Exited Succeeded` (`verification/de-novo-review-4/model-probes-out.txt:30-37`) | Row 32 added; documentation obligations expanded |
| P6 fails: a local claim may fire neither trigger 2 nor 3 | The report's diagnostic-string example | P6 and trigger 4 fall back to the project floor |
| P7 fails as a statement about support | F13's recorded outcomes are observations whatever the checker | Step 4 restated as a discharge policy |
| Finding 1: a local deadline leaves the same journal as a cut before it | `codex/probes-2.mjs`, rerun here | Row 25 proposes a journaled deadline for the owner's decision; row 23 is limited to journaled causes |
| Finding 2: protected invocation and exactly-once application differ | `spike/RESULTS.md:21`: the callback ran twice, applied once only under a stable target key | Row 8 split into five guarantees; row 7 scoped to attempts that continue |
| Finding 3: rows 2 and 16 disagree on released runs, and row 3 claims equality, not order | `derivation-v2.md` rows 2, 3, 16 | Delivery and retention separated; row 3 claims journal order |
| Finding 4: retry and cut claims miss reachable cases | Row 15(d) cited A9, which is a dropped run at suspension | Rows 15 and 18 scoped to failures the executor holds; suspension added; two failing closures listed |
| Finding 5: row 31 misstated the source and the theorem | `src/adapter/State.ts:65` (the adapter's own fiber counter); `conformance/host.ts` (one LCG for all draws); S10 in `verification/proofs/Scheduling/Statements.v` | Row 31 rewritten on S10's same-inputs property |
| Finding 6: the reported outcome is executor-selected and has no row | As for P5 | Row 32 |
| Finding 7: scopes used to waive trigger 2 and to demand proofs of observations | Rows 24, 26, 28 | Trigger 2 restored; row 26's trigger 3 limited to executor decisions |
| Finding 8: F9 already has an in-scope check; #36's gate fix exists | `codex/probes-2.mjs`, rerun here; `test-check-axioms-coq.sh:101-113` | Step 4 and the known weaknesses corrected |
| Finding 9: rows 11 to 14 weakened the inherited time guarantee | S8 in `verification/proofs/Scheduling/Statements.v`; `max_chunk` is 2147483647 (`Model.v:118`) | Rows 11 to 14 restated from S8's five parts |
| Finding 10: documentation exemptions too broad | Comments 7120209653, 7121743796, 7132209348 | Policies that decide something moved to rows; documentation list expanded |

