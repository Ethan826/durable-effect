# Integration spike results

Milestone 1 of [PLANNING.md](../PLANNING.md), run 2026-11-21.

**Versions:** effect 4.1.5, @effect/platform-node 4.1.5, @restatedev/restate-sdk 1.18.4, @t0ster/restate-effect 0.9.0, restate-server 1.8.1 (npm binary, no Docker), Node 26.6.0, TypeScript 7.0.2.

**Setup:** The server ran with `RESTATE_WORKER__INVOKER__INACTIVITY_TIMEOUT=0s`, which is what the testcontainers `alwaysReplay` option sets. The invocation suspends after every await, so each step starts a new attempt that replays everything before it. `src/durable.ts` wraps a handler and provides two services:

- **Clock.** One journaled sample (`Restate.run("clock-sample")`) at entry and one after each durable sleep. Reads between samples return the last sample. `Clock.sleep` is `Restate.sleep`. Monotonic time is the maximum sample seen so far.
- **Random.** One ISAAC stream per attempt, seeded with the invocation id (`Random.withSeed`).

No change to t0ster/restate-effect was needed. `Effect.provideService` over its handler Effect is enough. `src/trace.ts` logs every clock read, random draw, sleep delay and typed failure for each attempt, and `scripts/inspect.mjs` checks that each attempt's trace is a prefix of the final attempt's.

## Results

| Case | Outcome |
| --- | --- |
| Jittered exponential retry: 2 failures, then success | Passed. 9 attempts, all prefixes of the last. Same draws (0.4203…, 0.4315…) and delays (193.63 ms, 389.04 ms) on every replay. External service called 3 times, never on replay. |
| Immediately completed step | Passed. 3 attempts, journal is `clock-sample, charge, Output`. |
| Retries run out, ending in a recorded failure | Passed. 9 attempts. The caller receives the typed `Flaky` failure with its fields. |
| Crash after the external write, before the step is persisted | Passed. The callback ran twice (`calls: 2`), the external service applied the write once under the stable key `<invocationId>:hold:<key>` (`applied: 1`), and the journal holds one `hold` step. |
| Clock source moves backward across a sleep (5000, then 2000) | Replay was deterministic. `Clock.currentTimeMillis` went from 5000 to 2000, and `Effect.timed` around a 100 ms durable sleep reported **0 ms** (see findings). |

## Findings

1. **Replacing the two services is enough for the sequential case.** `Effect.sleep`, the `Effect.retry` schedule driver and `Schedule.jittered` all used the supplied Clock and Random, and every replay reproduced the earlier attempts exactly. This settles the first row of the plan's status table for this subset.
2. **Effect owns retries without extra adapter code.** `Restate.run` with a declared `error` schema and no `retry.while` journals the declared failure as the step's result, and the SDK does not retry it. Each failure reaches `Effect.retry` as a typed failure once per attempt. Defects keep their own path through `runRetry` and `onDefect`.
3. **Clock reads add no journal entries.** The run made 33 clock reads, and all of the journal's clock entries are the chosen refreshes. The cost is one `Run` command plus its completion per refresh. In the 3-try retry, refreshes were 3 of the 8 commands.
4. **The journal does not hold timer delays.** Restate journals `Sleep.wake_up_time`, which the SDK computes from the real clock when the command is created, and it doesn't compare that value on replay. Delays had to be compared through the trace, so a replay test needs this instrumentation; the journal alone can't show the delays.
5. **Elapsed time is wrong under the max-of-samples monotonic clock.** When the source moves backward, monotonic time stays frozen, so a real 100 ms sleep measures as 0. Any elapsed-time schedule (`Schedule.during`, `Effect.timed`) can undercount. Options: advance logical time by at least the slept duration, or derive monotonic time from durable sleep totals. This belongs to milestone 2.
6. **Test sources must keep state outside the attempt.** Every attempt calls the handler again. A sample source or fake that keeps state in a closure created per call restarts, which made the first backward run look wrong. The same applies to any stateful service an author builds inside a handler.
7. **Jitter produces fractional milliseconds** (193.627881). The SDK accepted them. Whether it rounds or truncates when computing `wake_up_time` hasn't been checked.

## Not covered

- **Telemetry.** Spans and log timestamps created inside the handler now read the logical clock. The handler's own server span is created outside the override and keeps real time. Nobody has inspected the actual span output.
- **Refreshes.** The refresh after a `run` completes, after calls or awakeables, and after a durable join is not implemented. Only entry and post-sleep refreshes exist.
- **Concurrency, `Effect.timeout`, and the lint/type gap probes.** All out of scope for this spike.
- **Restate in normal mode.** Every run used always-replay, which is the stricter mode, and there was no comparison against a run without forced suspension.

## Reproduce

```sh
npm ci
MODE=replay scripts/restate.sh &          # Restate on loopback
node src/server.ts &                       # endpoint on :9080
curl localhost:9070/deployments -H 'content-type: application/json' -d '{"uri":"http://127.0.0.1:9080"}'
scripts/cases.sh retry '{"key":"r2","failures":2,"times":4}'
scripts/cases.sh backward '{"samples":[5000,2000]}'
# crash window: touch data/crash-w1, POST /Spike/write/send {"key":"w1"}, restart the endpoint, attach
```
