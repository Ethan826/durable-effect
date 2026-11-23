# Dependency review records

Format from the dependency-intake skill. Each line states only what was
checked on 2026-11-22; "not checked" marks the rest.

## fast-check

- Why: the conformance and oracle tests need generated inputs and shrinking
  (AGENTS.md asks for property tests on the time rule, the guard and replay).
  Bun's test runner has no generator, and a hand-written one would be a
  component with no published source.
- Alternatives considered: hand-rolled random generators (no shrinking, no
  published source, so ruled out by compose-published-primitives); example-only
  tests (cannot cover the input space the rules name). Other property-test
  libraries for TypeScript: not checked.
- Footprint: dev-only. One transitive package, `pure-rand` 8.4.2 (MIT, no
  dependencies). Unpacked size of fast-check 4.11.0 is 1.5 MB. Nothing ships
  to users.
- Fit: imported only from test files. Uses `fc.assert`, `fc.property` and
  arbitraries. Registry metadata lists no peer dependencies.
- Release cycle and maintenance: latest release 4.11.0, published
  2026-11-21 (the `latest` dist-tag). The package dates from 2017. One npm
  maintainer is listed. Release cadence over the last year: not checked.
  Upgrades touch tests only.
- Security and supply chain: the registry metadata for 4.11.0 lists no
  `install`, `preinstall` or `postinstall` script, and the release has
  SLSA provenance. No downloaded binaries. Network access at runtime: not
  checked, but nothing in the tests passes it a URL.
- License: MIT, compatible.
- Pinning: exact `4.11.0` in `devDependencies`, with the integrity hash in
  `bun.lock`. An upgrade is a review.

## @types/bun

- Why: `tsc --noEmit` cannot resolve `bun:test` without Bun's type
  declarations, and the brief makes `bun run check` pass on the test file.
- Alternatives considered: writing the smoke test against `node:test`
  (needs `@types/node` anyway, and AGENTS.md says to use bun for unit
  tests); a local `declare module "bun:test"` stub (a hand-written type that
  can drift from the runtime).
- Footprint: dev-only. Adds `bun-types` 1.3.6 and `@types/node` 26.6.6, which
  brings `undici-types` 8.9.0. Declaration files only.
- Fit: imported only through the `types: ["bun"]` entry in `tsconfig.json`.
- Release cycle and maintenance: 1.3.6 matches the installed Bun runtime
  (1.3.6), so the types describe the API the tests run on. The Bun team
  publishes it; cadence: not checked. Upgrade with the runtime.
- Security and supply chain: registry metadata for `@types/bun` lists no
  scripts. `bun-types` 1.3.6 lists no install hooks (only `fmt`, `test`, `build`,
  `prebuild`). `@types/node` install scripts: not checked.
- License: MIT, compatible.
- Pinning: exact `1.3.6` in `devDependencies`, hash in `bun.lock`.

## typescript-ast (alias of typescript 6.0.3)

- Why: `scripts/vendor/tsdoc-gate.ts` decides on the TypeScript syntax tree, and
  typescript 7.0.2 has no classic compiler API (its main export is only the
  version). 6.0.3 is the last release of the JavaScript compiler.
- Alternatives considered: rewriting the gate on 7.0's `unstable/sync` API
  (unstable, reaches syntax trees only through a project server); another
  parser (a different syntax tree than the one `tsc` uses). Neither checked
  further.
- Footprint: dev-only, used only by `scripts/`. Nothing ships to users.
  Install size: not checked.
- Fit: imported as `typescript-ast` by the gate; `tsc` and `bun run check`
  keep using typescript 7.0.2.
- Release cycle and maintenance: no further 6.x releases are expected. Cost:
  syntax that TypeScript 7.x adds later may be misparsed by the gates until
  the alias moves.
- Security and supply chain: install scripts: not checked.
- License: Apache-2.0, compatible.
- Pinning: exact `npm:typescript@6.0.3` in `devDependencies`, hash in
  `bun.lock`.
