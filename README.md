# durable-effect

durable-effect aims to let you write [Restate](https://restate.dev) services in
ordinary [Effect](https://effect.website) (TypeScript, Effect v4) and have that
code replay correctly. Inside a handler, `Effect.sleep`, `Effect.retry` with
jittered schedules, `Clock` reads and `Random` draws should give the same results
on every replay, without a second API for time or randomness. It will be a
standalone package built directly on `@restatedev/restate-sdk`.

## Status

The project is at the design stage. There is no package code yet and nothing to
install. The v1 design is a draft under review:

- Epic [#21](https://github.com/Ethan826/durable-effect/issues/21) links every
  v1 decision and deferral.
- Design [#1](https://github.com/Ethan826/durable-effect/issues/1) holds the
  spec in a comment on the issue.

## Time and randomness

The [integration spike](spike/RESULTS.md) showed that replacing Effect's `Clock`
and `Random` services in each attempt is enough to make a sequential handler
replay exactly. The design keeps that mechanism and settles what time means
inside a handler.

Each attempt keeps a logical time computed from journaled clock samples, so a
replay reads the same values. A journaled step samples the clock when the attempt
starts and again after every `run`, sleep or call. Time advances at each awaited
durable operation and stays fixed between them, the model Temporal and Azure
Durable Functions use. It never decreases, and after a sleep it has grown by at
least the requested duration.

Each attempt draws randomness from one stream (Effect's `Random.withSeed`)
seeded with the invocation id. Draws repeat on replay as long as the code
consumes them in the same order, which v1 ensures by allowing only sequential
durable code.

Issue [#1](https://github.com/Ethan826/durable-effect/issues/1) has the full rule,
its bounds and the oracle results behind it.

## Repository layout

| Path | What it holds |
| --- | --- |
| `spike/` | A throwaway integration spike against a real Restate server. Results are in [spike/RESULTS.md](spike/RESULTS.md). |
| `verification/` | Models and probes for the design's algorithmic claims: two time-rule oracles and the scripts from the de novo reviews. See [verification/README.md](verification/README.md). |
| `PLANNING.md` | The original plan, partly superseded. Where it disagrees with the issues, the issues are current. |
| `INVESTIGATION.md` | The investigation that checked the first plan against Effect and Restate source. |
| `AGENTS.md` | Instructions and project rules for agents working in the repository. |

## Reproducing the evidence

The project uses bun, but the spike is throwaway and uses npm and Node. From
`spike/`:

```sh
npm ci
MODE=replay scripts/restate.sh &          # Restate on loopback
node src/server.ts &                       # endpoint on :9080
curl localhost:9070/deployments -H 'content-type: application/json' -d '{"uri":"http://127.0.0.1:9080"}'
scripts/cases.sh retry '{"key":"r2","failures":2,"times":4}'
scripts/cases.sh backward '{"samples":[5000,2000]}'
```

[spike/RESULTS.md](spike/RESULTS.md) lists the versions used and how to run the
crash-window case.

The first time-rule oracle takes about 90 seconds and the second takes several
minutes. From `verification/time-rule-oracle/`:

```sh
node oracle.mjs
node oracle-v2.mjs
```

The scripts in `verification/de-novo-review-*/` need `spike/node_modules`, so run
`npm ci` in `spike/` first. [verification/README.md](verification/README.md) says
what each one shows.

## Prior art and credit

- [t0ster/restate-effect](https://github.com/t0ster/restate-effect) (MIT). The
  design re-implements several of its ideas: typed errors encoded in
  `TerminalError` metadata, the one-pending-operation guard and the
  abandoned-operation rule, the `onDefect` policy, and contracts and serving.
  durable-effect does not depend on it or copy its code.
- Temporal, whose workflow time advances only when the code awaits, whose
  sandbox replaces `Math.random` with a seeded PRNG, and which exposes real time
  for telemetry beside deterministic time.
- Azure Durable Functions (Durable Task), which takes orchestration time from
  the latest `OrchestratorStarted` timestamp, computes timers from that time, and
  derives GUIDs from the instance id.

The provenance table in [#1](https://github.com/Ethan826/durable-effect/issues/1)
names the source of every algorithmic component.

## Contributing

Read [AGENTS.md](AGENTS.md) first. Designs and decisions are GitHub issues, not
committed files.

## License

[MIT](LICENSE)
