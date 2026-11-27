# The step 7 check of design revision 6

The bounded exhaustive check of revision 6's rules and statements (#48; the published grammar,
bounds and exclusions are comment 7144185705). Plain Node ESM, no dependencies. Run from this
directory with Node 26.

## Parts

The three parts import nothing from one another.

- `env.mjs`, `rules.mjs`, `model.mjs`: the model of Restate and the SDK (from the assumptions
  register) and of revision 6's executor, as a nondeterministic state machine: `initial`,
  `choices`, `step`, `history`, `streamOf`, `stateKey`, `programs`, `MUTANTS`, `limits` (reduced)
  and `fullLimits`. Written by one author. The executor's code is in `rules/`, split into
  modules by section; `rules.mjs` re-exports its interface from them.
  `ticks.mjs` is the one place the tier's tick rule is stated; `tier.mjs`
  and `tick.check.mjs` both import it.
- `predicates.mjs`: one predicate per statement over a whole history; `monitors.mjs`: the same
  claims as online folds over the event stream. Written by a second author who never read the
  model. `HISTORY.md` fixes the history and stream format between the two.
- `merged.mjs`: exhaustive search that merges a node when its model key and every monitor state
  match one already explored. `tier.mjs` runs it over every program within bounds on worker
  threads. `check.mjs` is the first, unmerged gate and is superseded by `tier.mjs`.

## Tools (`tools/`, run from this directory)

- `judge-witnesses.mjs`: judges every mutant's witness; the base must pass and the mutant fail.
  On 2026-11-24, 19 of 20 mutants are caught; `handlerScheduler` (M8) is not.
- `estimate-tier.mjs`: estimates a tier's cost from a seeded sample of programs. Run it before
  the 3-statement tier.
- `random-walks.mjs`, `smallest-witness.mjs`, `replay-path.mjs`: random walks through the
  predicates, the smallest rejected history for one predicate, and replaying a path that
  `tier.mjs` printed.

## Self-checks (each shown able to fail)

| Check | Command | Its control |
|---|---|---|
| Predicates accept correct and reject violating histories | `node predicates.test.mjs` | each predicate has its counterexample |
| Monitors agree with predicates | `node monitors.test.mjs` | blind S7, P2 and S12 monitors must disagree |
| Equal state keys have identical futures | `node statekey.check.mjs` | `... broken` drops true time and must fail |
| Clock readings and ticks change nothing else | `node slice.check.mjs readings` / `ticks` | `readings-control` and `ticks-control` must fail |
| Merging hides nothing | `FREEZE=1 node merged.check.mjs 4 150000` | `UNSOUND_KEY=1 ...` must exit 1 |
| Every mutant differs from the base model | `witnesses.mjs` (`replayWitness`) | each witness differs by construction |
| Verdicts | `node tick.check.mjs 2 2 2` | `node tick.check.mjs control 1 2 1` |

## Reductions in force, each with its justification

- One clock reading except in the clock tier: `slice.check.mjs readings` holds on 28 programs.
- No ticks while only clock samples execute: a premise, "a clock reading completes within the
  inactivity timeout" (owner, 2026-11-24; register entry to be filed).
- No ticks for programs with no run that lack a sleep or a clock read:
  only R1's stall reads ticks, and it needs an executing run's closure.
  Ticks still move true time, which the predicates read (S8's P5), so the
  check is by verdicts: `tick.check.mjs` explores each program the tier
  runs without ticks under the base model and every mutant, with ticks and
  without, and requires the same failing statements. It selects the
  programs through `ticks.mjs`'s `dropsTicks`, the function `tier.mjs`
  uses, so it checks exactly the tier's set.

  The rule used to cover every program with no run. de-2 checked that
  wider set, and the figures below come from it. At 1 fiber, 3 statements
  and 1 operation it found a difference in programs with a sleep, an
  await and a clock read, so the owner decided (issue #49) that those
  programs keep their ticks. The owner's runs on the new set are recorded
  in the commit that made this change and in #49.
  - At 2 fibers, 2 statements and 2 operations it holds: 128 programs,
    ticks change the leaf count in 840 runs, none is over the cap, and in
    every comparison the failure sets are equal. This is a bounded result
    only. Samples record true time even without a clock read:
    `[sleep s1 0ms, await s1]` can sample true times 0 to 3 with ticks
    and only 0 without.
  - At 1 fiber, 3 statements and 1 operation (460 programs) it fails: the
    reduction is not exact. Ticks change the leaf count in 1,828 runs, and
    3 runs differ, all under the `deliveryAnchor` mutant with readings
    {0, 2, 3} on `[sleep s1 (1, 2 or 3 ms), await s1, clock]`. With ticks
    they fail S8.P5 and S8.P6, without ticks only S8.P6, so dropping ticks
    hides an S8.P5 failure. 20 runs are over the cap: one program
    (`sleep s1 3ms`, then `await s1` inside `uninterruptible`) under the
    base model and 19 mutants. The base model shows no difference in the
    comparisons that completed; its run of that program is unchecked.
  - de-2's control, `hostTime`, made a clock statement add the host clock
    to L. At 1-3-1 it found 24 runs that differ, all in programs with
    both a sleep and a clock read, so it cannot fail in the new set.

  The control is now `hostTimeLink`: a sleep link is shortened by the
  host clock. At 1 fiber, 2 statements and 1 operation (64 programs in
  the new set) it finds 6 runs that differ, on `[sleep s1 (1, 2 or 3 ms),
  await s1]` in both readings sets. Each fails S2 with ticks (the 3 ms
  sleep also fails S8.P3P9) and fails nothing without. With its hunk in `rules/statements.mjs` reverted, it finds
  none and exits 1.

  `slice.check.mjs ticks` compares the executor's histories with ticks
  and without, with `sample.trueTime` and the warnings projected away, on
  3 named programs and 20 drawn from the 1,882 programs with no run at 2
  fibers, 3 statements and 3 operations. It draws from all programs with
  no run, a superset of the set the tier explores without ticks. A drawn
  program is kept only if ticks add leaves to its tree; too few draws, or
  a row with equal leaf counts, fails. It holds with no vacuous row.
  `ticks-control` runs it on programs with a run, where ticks are
  observable; 4 of 5 differ.
- Fewer ticks while nothing can observe them (`observableTicks`): a coverage reduction, not
  exact, documented in `env.mjs`.

## Results so far (`results/`)

- `tier.mjs 2 2 2`: all 1,052 programs at 2 fibers, 2 statements, 2 operations. Run 1 found a
  model bug (closing ran a turn during the freeze); run 2, after the fix, passes: 10,181,831
  nodes, none over the cap. Boundaries not reached at this size: a cancel during unwinding, a
  compensation send, a race's loser, an uninterruptible region. They need 3 statements.
  Run 3 (2026-11-26), with ticks kept for programs that have a sleep and a clock read
  (`ticks.mjs`), passes with the same node count: at these bounds ticks change no tree of
  those 8 programs.
- `merged.check.mjs`: 92 (program, model) pairs, 23 with failures, 0 different; 12 pairs over
  the unmerged cap were skipped. The unsound control finds 4 differences and exits 1.

The 3-statement tier (39,619 programs) has not run yet; its cost is being estimated.
