# Proposal: the evidence each component of revision 6 must have

Draft for independent review, 2026-11-24. Not yet approved. Once the review is settled, this goes to #48 as the step 4 standard.

## Where this fits

durable-effect runs Effect v4 handlers on Restate so that they are replay-safe. Design revision 6 (#48) moves the executor to one race per turn over every pending durable operation. Step 4 of #48 is a provenance table: each component of revision 6 with its closest published source, its fidelity (faithful, adapted or invented) and the standard alternative. The draft table is comment 7121785952 on #48.

The table says where each component comes from. It does not say what evidence each component needs before revision 6 can rely on it. The project rules (`AGENTS.md`) set a floor for the whole project. Anything that decides, orders or guarantees something needs an oracle or property test that shares no logic with the implementation, and a provenance entry. Evidence comes before proofs: no statement may depend on a Restate or SDK behaviour until a live fixture with a failing control has checked it. The target is a proved and tested v1 by 2026-12-13, so the proof effort has to go where it matters. This proposal sets the per-component requirement.

## A scoring scheme, considered and rejected

The first draft scored each component on three axes and added the scores. Importance (C1 to C3) set a base level of evidence, novelty moved it one step up or down, and risk moved it again, with clamps and floors. The owner rejected it. The axes are ordinal: nothing makes the step from adapted to invented the same size as the step from C2 to C3, or lets a point of risk cancel a point of novelty. The clamps and floors were there because the sums gave wrong answers. So the author's judgement was making the decisions, and the arithmetic only made them look more precise than they were.

## The proposal

### The evidence types catch different errors

The evidence types do not form one ladder. Each catches a class of error the others miss.

| Evidence | The error it catches | What misses that error |
|---|---|---|
| A register entry and a live fixture with a failing control | A wrong belief about how code we do not control behaves: the Restate server, the SDK, the Effect runtime | A proof, which takes the belief as an axiom; a bounded check, which encodes the same belief |
| A bounded exhaustive check that shares no logic with the executor (step 7 of #48) | A counterexample within a small scope: an interleaving, an attempt boundary, a replay | Example tests, which cover the cases someone thought of |
| A mechanised Coq proof with no `admit`, its axioms reported by the prover, a non-vacuity check, and differential tests that tie the extracted executor to the TypeScript one | A counterexample beyond the checked scope | A bounded check, by construction |
| An adaptation note: the source's argument, and each of its preconditions that our change touches, each closed by a lemma or a fixture | A precondition of a borrowed argument that our change breaks | Citing the source, which shows only that the argument held there |
| Adversarial procedure review, a recorded fallback, and the owner's approval | A wrong claim or definition, which no test was written to catch | Every test and proof, which check the claim as written |

Some of these errors have already happened here. The fourth de novo review (#30) found that the proofs held for a model that left out behaviour the design relied on. Probes of the model and of the running system caught it; the proofs could not have. R6's first run (`spike/rev6/rerun/run-out-1.txt`) refuted a belief about Restate's inactivity timer that a proof would have taken as an axiom.

### Each claim triggers the evidence it needs

Each claim a component makes is checked against five triggers. The component's requirement is the union of what its claims trigger. No weighting is involved.

1. If the claim depends on how the Restate server, the SDK or the Effect runtime behaves, it needs a register entry and a fixture with a failing control: live against a Restate server, or an in-process probe for the Effect runtime. In the proofs that behaviour is a named axiom.
2. If the claim quantifies over interleavings, attempts, replays or journal contents, it needs the bounded exhaustive check.
3. If a counterexample beyond the checked scope would go unnoticed and would lose or duplicate an external effect, lose a journal record, or make replay diverge, the claim needs a proof.
4. If the claim rests on a source's argument and our change touches that argument's preconditions, it needs an adaptation note. A source counts as an argument only if it states a guarantee and supports it, as a paper or a specification does. Code with no stated guarantee is precedent: it shows the design has been used, but it supplies no argument, so the argument for the claim has to be our own.
5. If no source has the component, it needs adversarial review, a recorded fallback and the owner's approval.

Only trigger 3, the proof line, is a judgement about consequences, and the owner draws that line once, not per component. The other four can be read off the claim and its sources. The approach follows assurance standards such as DO-178C, which set a software level from the severity of a failure condition and attach a list of specific objectives to each level, rather than computing a score.

### Applied to revision 6

`derivation.md` applies the triggers to the 24 components: the 22 rows of the step 4 table and the two executor rules added on 2026-11-24 (re-abort on replay, and a second warning). It lists the claims that set off each trigger and the evidence already in hand.

## Claims this proposal makes

- P1: For each evidence type, there is an error it catches and every other type misses, so no type can stand in for another.
- P2: Triggers 1, 2, 4 and 5 can be decided from a claim's text and its cited sources, without a weighting and without judging consequences.
- P3: The proof line in trigger 3 selects exactly the components where an error beyond the checked scope would be silent and would cost an external effect, a journal record or replay determinism.
- P4: Every requirement in `derivation.md` follows from the triggers, and no trigger that fires is left out.
- P5: `derivation.md` covers every component of revision 6 decided so far.
- P6: Code with no stated guarantee supplies no argument, so a component whose only source is code needs an argument of its own.

## Known weaknesses

- The time rule falls outside the proof line as written. A wrong time is silent, but it does not lose an effect or a record, or make replay diverge. Revision 5 proves the time rule anyway, and the registered fallback (prove it for one operation in flight, test the rest) assumes a proof is wanted. The owner has to decide whether the line includes the time rule. If it does, the line should name it.
- "Silent" is judged by the author for each component. `derivation.md` gives the reason for each judgement, so it can be challenged.
- The scope of the bounded check is not set. A bounded check is only as strong as its bounds, and this proposal does not say how many operations, fibers or attempts it must cover.
- The evidence is only as good as the gates that run it. The proposal assumes the fixtures, oracles and the axioms gate can fail when they should. The fourth review found an axioms gate that passed a module-level hypothesis of `False` (#30).
- One trigger 1 case is unsettled. Behaviour of the Effect runtime counts as external behaviour, but some of it (interruption, finalizers) is a documented guarantee of a library we depend on. This proposal still requires a probe for it.
