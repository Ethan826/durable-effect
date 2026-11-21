# Verification evidence

Evidence for the algorithmic claims in the v1 design (see the design issue on GitHub). These are
models and probes, not the package's tests. When implementation starts, each claim becomes a
property test against the real code.

- `time-rule-oracle/oracle.mjs`: brute-force oracle for the logical-time rule. It models Restate's
  journal, a host clock with error, and a crash and replay at every journal index. It shares no
  logic with any implementation. Run `node oracle.mjs` (about 90 s).
- `de-novo-review-1/`: scripts the first de novo reviewer wrote against effect 4.1.5. They need
  `spike/node_modules`, so run `npm ci` in `spike/` first. `leak.mjs` shows a `run` action
  inheriting the durable Clock and Random (F1). `race.mjs` and `race2.mjs` show `Effect.race`
  swallowing the guard's defect (F2). `skew.mjs` covers timer skew (F3), and `dur.mjs` covers zero
  and negative durations (F4). `oracle-out.txt` is the reviewer's rerun of the oracle.
