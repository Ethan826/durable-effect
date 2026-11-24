Step 4, the evidence standard, decided by the owner on 2026-11-24: what evidence a claim in revision 6 needs before the design can rely on it. The provenance table (comment 7121785952) says where each component comes from; this says what each claim must be backed by. Two independent reviews shaped it; their reports and probes are in `verification/evidence-standard-review/codex/` on branch `spike-gaps`. The design questions those reviews raised go to step 5 and are listed in the next comment.

The owner rejected an earlier draft that scored each component on importance, novelty and risk and added the scores. The axes are ordinal, so their points cannot be added, and the clamps the sums needed showed that judgement, not arithmetic, was making the decisions. This standard replaces the score with rules that each give their reason.

### 1. State the claim and its scope

The rules apply to claims, not to component names, and one component can make several claims that need different evidence. Each claim is written in terms an observer outside the executor can check (journal entries, external effects, values returned to handler code, warnings), with its scope:
- the programs it covers: which operations, how many fibers, what finalizers may do;
- the attempt boundaries it covers: success, suspension, an attempt ended by Restate's abort timeout, a crash, a kill, and the replays that follow;
- the SDK and server versions and settings it assumes.

A claim with no stated scope goes back to its author.

### 2. What each kind of evidence establishes

| Evidence | What it establishes | What it assumes |
|---|---|---|
| A register entry and a fixture with a failing control: live against Restate, or an in-process probe for the Effect runtime | That the external system behaved as stated in the shapes run, at the pinned versions | That the shapes run cover the claim's scope, and that the checker rejects wrong answers inside it |
| A bounded exhaustive check that shares no logic with the executor (step 7) | That no counterexample exists within the stated grammar and bounds | That the grammar can express every behaviour in the scope |
| A Coq proof with no `admit`, its axioms reported by the prover, a non-vacuity check, and differential tests tying the extracted executor to the TypeScript one | That the claim holds for every input the model can express, given its premises | That the model expresses the approved behaviour, and each premise is backed by a register entry |
| An adaptation note | That each precondition of a borrowed argument still holds after our change | That the source's argument is sound |
| Adversarial review, a recorded fallback and the owner's approval | That an independent reader looked for a false statement, and that there is a way back | The reviewer's diligence |

The kinds overlap: an exhaustive check and a proof can establish the same property of the same finite model. The standard does not claim they are exclusive. Each rule below names the evidence that answers the question it raises, and requires that evidence.

### 3. The rules

A claim's requirement is the union of the rules that apply. No weighting is involved.

1. External behaviour. If the claim depends on how the Restate server, the SDK or the Effect runtime behaves, each such premise needs a register entry and a fixture with a failing control for the claim's scope. In proofs it is a named axiom. A premise is not itself proved, and a register entry never satisfies rule 3.
2. Beyond examples. If the claim quantifies over interleavings, attempts, replays or journal contents, it needs the bounded exhaustive check. The grammar, bounds and exclusions are published before the check runs, and the result reports coverage of each boundary in the claim's scope.
3. The proof line. A claim about an executor decision needs a proof if a violation could go undetected until after one of these has happened: an external effect is performed twice, performed when it should not be, or skipped; a journal record is lost; replay diverges; or handler code receives a wrong value from the executor.
   - A value counts if the executor produces or selects it: which result reaches which await, how a failure is classified (terminal or retryable, a cancellation or an ordinary failure), the outcome it reports, and the times, keys and random draws it generates. The test is whether the value could differ if the executor were wrong while Restate behaved as the register says. A payload passed through unchanged from the journal does not count; its evidence is rule 1 and a round-trip test of the codec.
   - Only two observers count as detecting a violation: the executor, through a check that runs before the action it guards, and Restate, through a journal mismatch that stops the attempt before its next command. Detection counts only if it prevents the harm. A report that lets the action go ahead does not count, and neither does a failure reported after the harm.
   - When the claim rests on rule 1 premises, the proof is a theorem about the executor given those premises.
4. Borrowed arguments. If the claim adopts a source's argument (a paper or a specification that states a guarantee and supports it) and our change touches its preconditions, it needs an adaptation note. Code with no stated guarantee is precedent: the claim records it, but it supplies no argument, so the argument comes from rules 2 and 3 where they apply, and otherwise from the property test or oracle the project floor requires.
5. Invention. If no source has the component, it needs adversarial review, a recorded fallback and the owner's approval. "No source" means none in the prior-art search (comment 7119246326) or in a search recorded with the claim, where a source counts only if it makes the same observable claim in a comparable scope. A claim that cites a near match says why it is not the same.

Rule 3 is the only judgement about consequences, and the owner set its terms once, here, not per claim. This follows assurance standards such as DO-178C, which set a level from the severity of a failure condition and attach a list of objectives to each level, rather than computing a score.

### 4. When a fixture discharges a claim

A fixture's output always records what happened in the shapes it ran. It discharges a claim's rule 1 obligation only if its checker has been shown to reject a wrong answer inside the claim's scope: a planted mutant, or an existing control that changes the answer while keeping the shape. F9 meets this: its main predicate rejects two swapped winners in a real replay log (`verification/evidence-standard-review/codex/probes-2.mjs`). R6 does not: its checker accepts any warning time from 3.5 s to 7 s, including one 3 s early, because its control showed only that a different timer policy fails (`verification/evidence-standard-review/codex/probes.mjs`). One mutant does not show a checker rejects every wrong answer; it shows the checker is not blind to the one the claim most needs.

### Worked examples

- Re-abort on replay. Claim: when an attempt executes a run again and the journal holds the cause that aborted it earlier, its signal is aborted before its closure starts. Rule 1: A10 (lazy closure start, live in F18) and R5. Rule 2: yes, over any number of attempts. Rule 3: yes. Without re-abort a replay can run the work again and then succeed with one journaled result, so two executions leave one record, and Restate's retry policy pauses the invocation only after any repeats. Rule 5: invented, approved 2026-11-24. R5 has no in-scope mutant yet, so under step 4 it does not yet discharge rule 1.
- The time rule. Claim: revision 5's S8 (monotone, floor, cancel, chunk bound and upper bound) holds in revision 6's model. Rule 3 applies because the time is a value the executor produces and handler code can branch on: two fully overlapping 10 ms sleeps credited as 20 ms send a handler with a 15 ms cutoff down the wrong branch, with an exact replay. Monotonicity alone would not do, since a clock stuck at 0 is monotone. The owner's fallback stands for the timing bounds: prove them for one operation in flight and label the concurrent claims tested.
- A diagnostic warning. Claim: within one attempt, an aborted run still running past a stated deadline is warned about once. Rule 2 applies, because deliveries, the abort, the timer and settlement can come in any order. Rule 3 does not: a wrong warning causes none of its harms. Rule 5: invented, approved, with the earlier warning as fallback.

### Known limits
- Rule 3 still takes judgement about when a violation is detected; each claim records that judgement so it can be challenged.
- No bounded-check grammar exists yet, so every rule 2 obligation waits on step 7 publishing one.
- The evidence is only as good as its gates. The axioms gate's hole found in #30 was fixed in #36 and its tests include that mutant; revision 6's new premises need the gate to check every reported axiom against an allowed list tied to register entries.
- Effect's documented guarantees still need probes, since #34 found a finalizer whose timing differed from the model's.
