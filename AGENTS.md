# durable-effect: agent instructions

Replay-safe Effect handlers on Restate. Read this before working in the repository.

Plans: issues

Designs and implementation plans live in GitHub issues, not in committed files (see Records).

## Records

- Decisions, deferrals and findings are GitHub issues under an `epic`, with a `tier: N` label or a
  status label (`decision`, `deferred`, `candidate`, `spike`). A deferral states its reason and what
  would reopen it. Where an issue's spec is a comment, the issue body says which comment.
- The v1 design is the spec comment on its design issue. The v1 epic links every decision.

## Project rules

- Build on `@restatedev/restate-sdk` directly. Never add a dependency on
  `@t0ster/restate-effect`. Its design ideas may be re-implemented with credit; its code is not
  copied.
- Use bun for install, scripts and tests. Tests that check behaviour on a specific
  runtime (Node support) run on that runtime. `spike/` is throwaway and uses npm and Node.
- Pin exact versions of every dependency and commit the lockfile. Treat an
  upgrade as a review.
- Follow the effect-v4 and readable-functional-code skills (typescript.md):
  - no v3 Effect names, no throwing in core code, decode instead of asserting;
  - at most depth 3, 8 branches, 30 lines and 8 local bindings per declaration;
  - at most 250 lines per module and 80 columns per line;
  - arrow functions and named steps;
  - TSDoc on every export, checked by a syntax-tree gate;
  - never a lint-disable comment.
- Follow test-first. Gates and lints must be shown able to fail (gate-integrity).
- Any component that decides, orders or guarantees something
  (the time rule, the guard, replay behaviour) is checked by an oracle or property test that shares
  no logic with the implementation, and has a provenance entry naming its published source
  (compose-published-primitives).
- New or changed algorithmic designs, and the claims made
  about them, are reviewed by an independent reviewer who decides each claim afresh from primary
  evidence and gives no deference to the author's reasoning (adversarial-procedure-review). Check
  each finding against the evidence before acting on it. Close it with a fixture or oracle property,
  not a document edit.
- Run the humanized-prose-review skill on every
  piece of prose another person will read (design docs, issues and comments, READMEs, this file,
  commit messages, PR descriptions) before filing, committing or publishing it. Put the most
  significant catalog entries in the commit body.

## Review by eye

These rules have no tool check yet:
- named steps in place of inline lambdas;
- comments that explain why, in plain words;
- no time, randomness or timers read outside the durable services in handler code.
