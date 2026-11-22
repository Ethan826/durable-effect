#!/bin/sh
# Checks the Coq executor model extracted to OCaml against the kernel (#37, the
# implementation link). For every equality witness in Executor/Witnesses*.v it reads both
# sides from the theorem's statement, extracts them, compiles natively, and compares the
# trace the extracted executor computes with the trace vm_compute checked. Witnesses that
# are not equalities are skipped by name. Then it runs a checker mutant, an extracted
# executor whose command comparison accepts anything, which must produce a mismatch.
#
# Run from verification/proofs, with the project's opam switch active and the project
# built. Exits 0 only if every case agrees, at least $FLOOR cases ran, and the mutant
# fails.
set -u
FLOOR=30
here=$(pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

fail() { echo "FAIL: $1" >&2; exit 1; }

{
  cat <<'EOF'
From Coq Require Import List ZArith String Extraction.
From Durable Require Import Runtime Exec Concrete Rev3 Witnesses Witnesses2.
Import ListNotations.
Open Scope string_scope.
Ltac case_of name th :=
  let T := type of th in
  let T' := eval cbv zeta in T in
  match T' with ?l = ?r => exact (name, l, r) end.
EOF
  names=$(grep -h '^Theorem' Executor/Witnesses*.v | sed 's/Theorem \([A-Za-z0-9_]*\).*/\1/')
  for t in $names; do
    echo "Definition c_$t : string * list Action * list Action :="
    echo "  ltac:(first [case_of \"$t\" $t | exact (append \"SKIPPED \" \"$t\", [], [])])."
  done
  echo "Definition cases : list (string * list Action * list Action) := ["
  printf '%s\n' $names | sed 's/^/  c_/; s/$/;/' | sed '$ s/;$//'
  echo "]."
  echo "Extraction Language OCaml."
  echo "From Coq Require Import ExtrOcamlBasic ExtrOcamlString."
  echo "Extraction \"durable_cases.ml\" cases."
} > "$work/Cases.v"

cat > "$work/main.ml" <<'EOF'
let name_of cs = String.of_seq (List.to_seq cs)
let () =
  let ok = ref 0 and bad = ref 0 and skipped = ref 0 in
  List.iter (fun ((n, computed), expected) ->
      let n = name_of n in
      if String.length n >= 8 && String.sub n 0 8 = "SKIPPED " then incr skipped
      else if computed = expected then incr ok
      else (incr bad; Printf.printf "MISMATCH %s\n" n))
    Durable_cases.cases;
  Printf.printf "agree=%d mismatch=%d skipped=%d\n" !ok !bad !skipped;
  exit (if !bad = 0 then 0 else 1)
EOF

cd "$work" || fail "no work directory"
coqc -R "$here/Executor" Durable -R "$here/Scheduling" Scheduling Cases.v >coqc.log 2>&1 \
  || { cat coqc.log >&2; fail "extraction failed"; }
ocamlfind ocamlopt -package str durable_cases.mli durable_cases.ml main.ml -o check \
  >ocaml.log 2>&1 || { cat ocaml.log >&2; fail "OCaml build failed"; }

out=$(./check)
status=$?
echo "$out"
[ "$status" -eq 0 ] || fail "the extracted executor disagrees with the kernel"
agreed=$(printf '%s\n' "$out" | sed -n 's/^agree=\([0-9]*\).*/\1/p')
[ -n "$agreed" ] && [ "$agreed" -ge "$FLOOR" ] || fail "only ${agreed:-0} cases ran, floor $FLOOR"

mkdir mutant && cp durable_cases.mli main.ml mutant/ || fail "no mutant directory"
sed 's/^let cmd_eqb a b =$/let cmd_eqb _ _ = true\nlet _cmd_eqb_orig a b =/' durable_cases.ml \
  > mutant/durable_cases.ml
grep -q '^let cmd_eqb _ _ = true' mutant/durable_cases.ml || fail "mutant not applied"
cd mutant || fail "no mutant directory"
ocamlfind ocamlopt -package str durable_cases.mli durable_cases.ml main.ml -o check \
  >ocaml.log 2>&1 || { cat ocaml.log >&2; fail "mutant build failed"; }
if ./check >mutant.out; then fail "checker mutant passed"; fi
grep -q '^MISMATCH different_journal_mismatches' mutant.out \
  || fail "checker mutant failed for the wrong reason"
echo "PASS: $agreed cases agree; the checker mutant fails"
