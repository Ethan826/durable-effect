# The proof gate

`check-axioms-coq.sh` is this project's proof gate, and `test-check-axioms-coq.sh` holds its tests. Both are pinned copies of the proof-dossier skill's scripts, taken on 2026-11-21 after the fix for #36. The project's own copy means a change to the skill cannot change what this gate checks; a change here is reviewed like any other change to a gate.

| File | SHA-256 when copied |
|---|---|
| `check-axioms-coq.sh` | `e090960150c65c08b8efdb9cb49d39586cea7d7f9c70ddac46251742cf676d66` |
| `test-check-axioms-coq.sh` | `cacdee1e36f24e661a5acf355f5026f9c0b7a5be7204a551bd08700c281fbb49` |

With the project switch active, run both from `verification/proofs`:

    bash gate/test-check-axioms-coq.sh
    gate/check-axioms-coq.sh _CoqProject axioms-report.txt theorems.txt

The tests build small Coq projects in a temporary directory and must report `0 failure(s)`. The gate must print `PASS`. It checks the sources for unproved assumptions and switched-off kernel checks, rebuilds from clean, compares the theorem list with the theorems Coq reports, audits the assumptions of every constant the modules declare, and compares the regenerated axioms report with `axioms-report.txt`.
