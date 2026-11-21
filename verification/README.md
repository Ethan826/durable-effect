# Verification evidence

Evidence for the algorithmic claims in the v1 design (see the design issue on GitHub). These are
models and probes, not the package's tests. When implementation starts, each claim becomes a
property test against the real code.

- `time-rule-oracle/oracle.mjs`: brute-force oracle for the logical-time rule. It models Restate's
  journal, a host clock with error, and a crash and replay at every journal index. It shares no
  logic with any implementation. Run `node oracle.mjs` (about 90 s).
- `time-rule-oracle/oracle-v2.mjs`: revision 2 of the oracle (issue #19), written from scratch.
  It checks every claim on replays as well as originals, and adds operation failures, retried
  sample steps, sleeps of zero, negative and infinite duration, deadlines computed from logical
  time, and replays on a different host. Five mutants show each check can fail. Output is in
  `oracle-v2-out.txt`; the run takes several minutes.
- `time-rule-oracle/oracle-v3.mjs`: revision 3 (issue #23), written from scratch. It adds calls
  that fail, cancellation at any operation, a sleep cancelled partway through, a sleep above
  2^53 - 1 ms, and replays on two hosts. It is a gate: it exits non-zero unless the adopted rule
  passes, every mutant fails its named claim, the run and replay counts match their pinned values,
  and the scan includes a named case. `CHECKER_MUTANT=P5 ONLY=floorOnCancel` disables one check
  and must exit 1. Outputs are in `oracle-v3-out.txt` and `oracle-v3-checker-mutant-out.txt`.
  Oracles 1 and 2 always exit 0, so they are report-only history.
- `de-novo-review-1/` and `de-novo-review-2/`: scripts the de novo reviewers wrote against effect 4.1.5. They need
  `spike/node_modules`, so run `npm ci` in `spike/` first. `leak.mjs` shows a `run` action
  inheriting the durable Clock and Random (F1). `race.mjs` and `race2.mjs` show `Effect.race`
  swallowing the guard's defect (F2). `skew.mjs` covers timer skew (F3), and `dur.mjs` covers zero
  and negative durations (F4). `oracle-out.txt` is the reviewer's rerun of the oracle.
