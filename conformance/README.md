# Conformance suite

This suite checks that Effect 4.1.5, run through the adapter in `src/adapter/`,
meets the runtime interface of issue #37. It generates programs from a grammar
of Effect combinators, runs each under a scripted host, and checks the
interface properties I1 to I9. Every property has the mutants #37 names, each a
broken adapter that must make its check fail. The result is bounded evidence:
it holds for these programs, seeds and journals, not for every program.

## Running it

```
bun run conformance         # everything
bun run conformance:quick   # everything except determinism.check.ts
```

Both run on Node (`node --test`), not bun. The suite tests how Effect and the
adapter behave on the runtime that deploys them, and Node is that runtime. The
determinism checks also start fresh Node processes, so the process under test
is the one that ships.

Bare `bun test` finds none of it, because the files end in `.check.ts` and bun
collects only `.test.ts`. `bun run test` covers the unit tests alone.

The full run takes about 14 minutes. `determinism.check.ts` is most of that
(about 11 minutes): it runs 5,000 programs four times each, and then every I1,
I2, I7 and I9 mutant until it fails. The quick run is for work on the other
files.

## What each file is for

Files that end in `.check.ts` are the tests:

- `determinism`: I1, I2, I7 and I9, and their mutants; the pinned I9 cases.
- `lifecycle`: I3, I4, I5, I6 and I8, and their mutants.
- `sequences`: arbitrary task sequences against the log properties of
  `Runtime.v`, tasks the executor never sends included.
- `closing`: the two pinned I8 cases that the grammar cannot reach.
- `fixtures`: runs that break exactly one comparison of an I1, I2, I7 or I9
  check, and the scan floor. `gate`: runs `fixtures` against copies of the
  checkers with one comparison turned off; each copy must fail.
- `grammar`: the grammar's inventory and bounds. `interpret`, `host`,
  `discard`, `opcount` and `logprops`: the harness's own tests.

The rest is the harness:

- Programs: `grammar`, `interpret`, `shapes`.
- Hosts and runs: `host`, `runs`, `worker`, `processes`, `plan`.
- Properties and checks: `properties`, `lifecheck`, `i3check`, `logprops`,
  `lifeplan`, `strays`.
- Oracles that do not share code with the adapter: `census`, `opcount`,
  `runloops`.
- Mutants: `mutants`, `lifemutants`, `guardmutants`, `renumber`,
  `liferegistry`.
- Pinned cases: `pinned` (I9), `closing` (I8).

## What it cannot catch

- A defect that no generated program reaches. The grammar has no way to start
  a fork masked, so `closing` pins the two cases #37 names for I8.
- Work that one counted operation hides. I9 counts operations, and a handler
  that does unbounded work inside one is outside the grammar.
- Anything about the Restate SDK or the executor. The live fixtures and the
  differential tests cover those.
- A property that holds for 5,000 programs per property and fails for the
  5,001st.
