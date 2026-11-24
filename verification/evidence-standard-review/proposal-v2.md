# Proposal: the evidence each component of revision 6 must have

Second draft, 2026-11-24, revised after the first independent review (`codex/report.md`). Not yet approved. Once the review is settled, this goes to #48 as the step 4 standard. The first draft is kept as `proposal-v1.md`, and the section "What changed after review 1" maps each finding to its change.

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
| Adversarial review, a recorded fallback and the owner's approval | That an independent reader found no false statement, and that there is a way back if one is found later | Only the reviewer's diligence; it is the only check aimed at a wrong claim or definition |

The first draft claimed that each kind catches an error all the others miss. Review 1 showed overlaps: a bounded check and a live fixture can both catch a replay comparison that ignores a call's payload. The claim is now weaker. Each kind rests on different assumptions, so using one where another is required leaves the other's assumptions unchecked. The project has seen this twice. The fourth de novo review (#30) found proofs that held for a model that left out behaviour the design relied on. R6's first run refuted a belief about Restate's inactivity timer that a proof would have taken as an axiom.

### Step 3: the triggers

Each claim is checked against five triggers. The claim's requirement is the union of what it triggers. No weighting is involved.

1. If the claim depends on how the Restate server, the SDK or the Effect runtime behaves, each such premise needs a register entry and a fixture with a failing control for the claim's scope. In proofs the premise is a named axiom. The premise itself is not proved, and a register entry never satisfies trigger 3.
2. If the claim quantifies over interleavings, attempts, replays or journal contents, it needs the bounded exhaustive check. The grammar, bounds and exclusions are published before the check runs, and its result reports coverage of each boundary the claim's scope names.
3. A claim needs a proof if a violation could go undetected, by the executor and by Restate, until after one of these has happened: an external effect is performed twice, performed when it should not be, or skipped; a journal record is lost; replay diverges; or handler code receives a wrong value from the executor. A value counts here if the executor produces or selects it: which result reaches which await, how a failure is classified (terminal or retryable, a cancellation or an ordinary failure), and the times, keys and random draws it generates. The test is whether the value could differ if the executor were wrong while Restate behaved as the register says. A payload the executor passes through unchanged from the journal (a run's result, a call's response, an awakeable's value) does not count; its evidence comes from trigger 1 and a round-trip test of the codec. Detection is judged at the first violation, by an observer who could stop the harm. A failure reported after the harm does not count: for example, Restate's retry policy pausing an invocation that has already repeated an external call. When the claim rests on premises from trigger 1, the proof is a theorem about the executor given those premises.
4. If the claim adopts a source's argument (a paper or a specification that states a guarantee and supports it) and our change touches that argument's preconditions, it needs an adaptation note. The trigger fires only when an argument is actually adopted. Code with no stated guarantee is precedent: it shows that a design has been used, and the row records it as precedent, but it supplies no argument, so the argument for the claim must come from triggers 2 and 3.
5. If no source has the component, it needs adversarial review, a recorded fallback and the owner's approval.

Trigger 3 is the only judgement about consequences, and the owner sets its terms once, not per component. The approach follows assurance standards such as DO-178C, which set a software level from the severity of a failure condition and attach a list of specific objectives to each level, rather than computing a score.

### Step 4: what makes a fixture count

A fixture supports a claim only if its checker has been shown to reject a wrong answer inside the claim's scope, not just a different policy. Review 1 found that R6's checker accepts any warning time from 3.5 s to 7 s, including one 3 s before the deadline it is meant to confirm. Its control showed only that a timer started from the last command sent fails. So each fixture's checker gets a planted wrong answer of its own (a mutant). A fixture whose checker has none is recorded as an observation, not as evidence for the claim. Probes of a checker, such as `codex/probes.mjs`, are kept beside the fixture and rerun with it.

## Applied to revision 6

`derivation.md` applies these steps to 31 components: the 22 rows of the step 4 table, the two executor rules added on 2026-11-24, six obligations review 1 found missing, and the deterministic `Random`, which the author found missing while applying trigger 3. For each it states the claim and its scope, the triggers that fire, the evidence in hand, and what is still open.

## Claims this proposal makes

- P1: Each kind of evidence rests on assumptions the others do not, so one kind cannot stand in for another without leaving those assumptions unchecked.
- P2: Once a claim and its scope are written down as in step 1, triggers 1, 2, 4 and 5 can be decided from the claim and its cited sources without judging consequences.
- P3: Trigger 3 requires a proof exactly where a violation could cause one of its listed harms before anyone who could stop the harm detects it.
- P4: Every requirement in `derivation.md` follows from the triggers, and no trigger that fires is left out.
- P5: `derivation.md` covers every component and approved obligation of revision 6 decided so far.
- P6: Code with no stated guarantee supplies no argument, so a component whose only source is code gets its argument from triggers 2 and 3.
- P7: A fixture whose checker has no mutant inside the claim's scope does not support the claim.

## Known weaknesses

- The owner set trigger 3's terms on 2026-11-24, including which values count. Applying them still takes judgement about who could detect a violation and when, and each row records that judgement so it can be challenged.
- No bounded check grammar exists yet. Until one is published, every T2 in `derivation.md` is an obligation with no means of discharge.
- The evidence is only as good as the gates that run it. The fourth review found an axioms gate that passed a module-level hypothesis of `False` (#30, #36). Step 4 requires mutants for fixture checkers; the axioms gate needs the same.
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
