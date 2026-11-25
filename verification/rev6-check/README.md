# The step 7 check of design revision 6

The bounded exhaustive check of revision 6's rules and statements (#48; the published grammar,
bounds and exclusions are comment 7144185705). Plain Node ESM, no dependencies. Run from this
directory with Node 26.

## Parts

The three parts import nothing from one another.

- `env.mjs`, `rules.mjs`, `model.mjs`: the model of Restate and the SDK (from the assumptions
  register) and of revision 6's executor, as a nondeterministic state machine: `initial`,
  `choices`, `step`, `history`, `streamOf`, `stateKey`, `programs`, `MUTANTS`, `limits` (reduced)
  and `fullLimits`. Written by one author.
- `predicates.mjs`: one predicate per statement over a whole history; `monitors.mjs`: the same
  claims as online folds over the event stream. Written by a second author who never read the
  model. `HISTORY.md` fixes the history and stream format between the two.
- `merged.mjs`: exhaustive search that merges a node when its model key and every monitor state
  match one already explored. `tier.mjs` runs it over every program within bounds on worker
  threads. `check.mjs` is the first, unmerged gate and is superseded by `tier.mjs`.

## Self-checks (each shown able to fail)

| Check | Command | Its control |
|---|---|---|
| Predicates accept correct and reject violating histories | `node predicates.test.mjs` | each predicate has its counterexample |
| Monitors agree with predicates | `node monitors.test.mjs` | blind S7, P2 and S12 monitors must disagree |
| Equal state keys have identical futures | `node statekey.check.mjs` | `... broken` drops true time and must fail |
| Clock readings and ticks change nothing else | `node slice.check.mjs readings` / `ticks` | `readings-control` must fail |
| Merging hides nothing | `FREEZE=1 node merged.check.mjs 4 150000` | `UNSOUND_KEY=1 ...` must exit 1 |
| Every mutant differs from the base model | `witnesses.mjs` (`replayWitness`) | each witness differs by construction |

## Reductions in force, each with its justification

- One clock reading except in the clock tier: `slice.check.mjs readings` holds on 28 programs.
- No ticks while only clock samples execute: a premise, "a clock reading completes within the
  inactivity timeout" (owner, 2026-11-24; register entry to be filed).
- No ticks for programs without a run: ticks are read only by R1's stall, which needs an
  executing run's closure; `slice.check.mjs ticks` holds on the 24 of 28 programs without one.
- Fewer ticks while nothing can observe them (`observableTicks`): a coverage reduction, not
  exact, documented in `env.mjs`.

## Results so far (`results/`)

- `tier.mjs 2 2 2`: all 1,052 programs at 2 fibers, 2 statements, 2 operations. Run 1 found a
  model bug (closing ran a turn during the freeze); run 2, after the fix, passes: 10,181,831
  nodes, none over the cap. Boundaries not reached at this size: a cancel during unwinding, a
  compensation send, a race's loser, an uninterruptible region. They need 3 statements.
- `merged.check.mjs`: 92 (program, model) pairs, 23 with failures, 0 different; 12 pairs over
  the unmerged cap were skipped. The unsound control finds 4 differences and exits 1.

The 3-statement tier (39,619 programs) has not run yet; its cost is being estimated.
