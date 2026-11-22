# Fourth de novo review: proofs and model at ca22341

Codex, run as an independent reviewer on 2026-11-21, wrote these probes. The main session reran each one at ca22341 and recorded the output beside it. The findings are issues under epic #21.

| File | What it checks | Rerun with |
|---|---|---|
| `model-probes.v` | The Coq model on small programs: one evaluation per finding, plus two kernel-checked goals (S4's trace predicate accepts two overlapping commands from one fiber, and a `single_fiber` witness) | `coqc -R verification/proofs/Scheduling Scheduling model-probes.v`, with the project switch active and the proofs built |
| `runtime-probes.mjs` | effect 4.1.5 and SDK 1.18.4 in process: task priority, immediate forks, `Fiber.interrupt` waiting for the finalizer, resumes outside a turn, and the SDK's JavaScript layer | `node runtime-probes.mjs` |
| `live-cancellation.mjs`, `live-cancellation.sh` | A local Restate server: cancellation during a wait, during a pending sample, and with an abandoned operation that has a listener and one that has none | `bash live-cancellation.sh`, from a scratch directory, since it writes logs to the current directory |
| `gate-mutant-append.v` | Appended to a scratch copy of `Scheduling/TimeRule.v`, it gives a module-level hypothesis of `False`, which the axioms gate passed at ca22341 | Copy the proof project, append the file, and run the gate |

The probes use absolute paths into this checkout and `spike/node_modules`.
