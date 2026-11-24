# Brief for the independent reviewer

You are reviewing a proposal for the evidence each component of a design must have before the design can rely on it. Your task is to find a false statement or a missing case. Do not check whether it looks right. Decide each claim afresh from primary evidence, and give the author's reasoning no weight.

## What to read

1. `AGENTS.md` at the repository root, for the project's rules.
2. `proposal.md` in this directory: the standard, its claims P1 to P6, and its known weaknesses.
3. GitHub issue #48 and its comments (`gh issue view 48 --comments`, or `gh api repos/Ethan826/durable-effect/issues/48/comments`), especially:
   - the assumptions register, comment 7119394545;
   - the step 3 decisions, comments 7120209653, 7121147686, 7121677014, 7121743796 and 7132209348;
   - the step 4 provenance table, comment 7121785952;
   - the fixture results, comments 7119858917, 7120729029, 7121240220, 7122123641 and 7136194021.
4. #30, the fourth de novo review, for errors the project has already made.
5. Only after step 1 of the task below: `derivation.md` in this directory.

The fixtures and their outputs are under `spike/rev6/` on the branch `spike-gaps`. The Coq proofs of revision 5 are under `verification/proofs/`.

## The task

1. Before you read `derivation.md`, apply the five triggers in `proposal.md` to at least eight components of the step 4 table. Include rows 6, 13, 19 and 22 of that table, counting from the top, and choose the others yourself. Write down your derivation. Then compare it with `derivation.md`, and report each difference with the reason for it.
2. Test each claim, P1 to P6. For each one, give one of these verdicts:
   - holds, with the evidence;
   - fails, with a concrete counterexample;
   - unsupported, with what is missing.
   For P1, look for an error that two evidence types both catch, or one that none of them catch. For P2, look for a trigger that cannot be decided without judging consequences. For P3, look for a component where the proof line gives a result the owner would reject: a proof for something harmless, or none for something that loses an effect or a record.
3. Look for missing components. Check `derivation.md` against the step 3 decisions and the register. Report any rule or behaviour that revision 6 relies on and that has no row.
4. For each row of `derivation.md`, check that the cited register entries and fixtures exist, and that they show what the row says they show. Read the fixture outputs (`run-out*.txt`) yourself; do not trust the comments' summaries.
5. For each known weakness in `proposal.md`, say whether it is stated accurately and whether it is worse than the proposal admits.

## Rules

- Do not edit any tracked file, commit, push, or comment on GitHub.
- You may write probes and notes in `verification/evidence-standard-review/codex/`. Leave them there for the author to rerun.
- Cite file paths with line numbers, issue comment ids, or the output lines that support each finding.
- If a finding depends on how Restate, the SDK or Effect behaves, cite the source or a probe. Do not rely on memory.

## The report

Write `verification/evidence-standard-review/codex/report.md` with:

1. your verdict on each claim, P1 to P6;
2. your derivations from task step 1, and the differences from `derivation.md`;
3. findings, most severe first, each with its evidence and the change it calls for;
4. anything you could not check, and why.
