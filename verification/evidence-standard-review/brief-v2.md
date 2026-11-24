# Brief for the second review

You are reviewing the second draft of a proposal for the evidence each component of a design must have. The first review is `codex/report.md`; the author revised `proposal.md` and `derivation.md` in response and kept the first drafts as `proposal-v1.md` and `derivation-v1.md`. Your task is to find a false statement or a missing case. Decide each claim afresh from primary evidence and give the author's reasoning no weight, including the author's account of what changed.

## What to read

1. `AGENTS.md` at the repository root.
2. `codex/report.md`, the first review.
3. `proposal.md`, the second draft: its steps 1 to 4, its claims P1 to P7, its known weaknesses, and its table "What changed after review 1".
4. `derivation.md`, the second draft, with rows 1 to 31.
5. GitHub issue #48 and its comments, as listed in `brief-v1.md`, and the fixture outputs under `spike/rev6/` on the branch `spike-gaps`.

## The task

1. For each finding in `codex/report.md` (the six claim verdicts, findings 1 to 7, and the table of missing obligations), say whether the second draft answers it, answers it in part, or does not, and why. A finding counts as answered by the document only where the document now states the obligation correctly; it is closed only by a fixture, a checker mutant or an oracle, and none of those has been added yet.
2. Test each claim P1 to P7 and give one of these verdicts: holds, with the evidence; fails, with a concrete counterexample; or unsupported, with what is missing. P7 is new.
3. Test trigger 3 as now worded, including the owner's decision on which values count (those the executor produces or selects, not payloads it passes through). Look for a component where it requires a proof for something that cannot cause its listed harms, or none where a violation causes one before detection, and for a value the executor produces that no row covers.
4. Check rows 25 to 31 and the documentation obligations against the step 3 decisions on #48. Report anything still missing.
5. Check every citation added in the second draft (file and line, comment id, fixture) against its source.
6. Say whether the second draft introduces any new error.

## Rules

- Do not edit any tracked file, commit, push, or comment on GitHub.
- Write probes and notes in `codex/`. Do not overwrite the first round's files.
- Cite file paths with line numbers, comment ids, or output lines for each finding.

## The report

Write `codex/report-2.md` with:

1. a table of the first review's findings and whether each is answered;
2. your verdict on each claim, P1 to P7;
3. new findings, most severe first, each with its evidence and the change it calls for;
4. anything you could not check, and why.
