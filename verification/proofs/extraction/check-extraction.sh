#!/bin/sh
# Checks the Coq executor model extracted to OCaml, natively and compiled to JavaScript
# through js_of_ocaml, against the kernel (#37, the implementation link). For every
# equality witness in Executor/Witnesses*.v and every equality evaluation in
# Executor/Rev3Counter.v it reads both sides from the statement (splitting a conjunction of
# equalities into one case each), extracts them, and compares the trace the extracted
# executor computes with the trace the kernel checked. A case whose expected side is itself
# a run of an executor (run = run, run = run3) compares extracted code with extracted code;
# it is counted apart, as a self-comparison. Statements that are not equalities are skipped
# by name. Compare.v is not covered: its old-model traces have another type.
#
# Then it runs a checker mutant, an extracted executor whose command comparison accepts
# anything, natively and in JavaScript; both must report a mismatch on
# Witnesses.different_journal_mismatches.
#
# Run from verification/proofs, with the project's opam switch active and the project
# built, and with Node on the PATH. Exits 0 only if every case agrees in both targets, at
# exactly $EXPECTED cases against the kernel ran (a pinned count, so coverage cannot
# shrink silently), and both mutants fail. Skipped statements are printed by name.
set -u
EXPECTED=57
STACK=8000
here=$(pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

fail() { echo "FAIL: $1" >&2; exit 1; }

# Each statement as Module.name, from the file it is in.
names=$(grep -H -E '^(Theorem|Lemma) ' Executor/Witnesses*.v Executor/Rev3Counter.v \
  | sed -E 's#^Executor/([A-Za-z0-9]*)\.v:(Theorem|Lemma) ([A-Za-z0-9_]*).*#\1.\3#')
{
  cat <<'EOF'
From Coq Require Import List ZArith String Extraction.
From Durable Require Import Runtime Exec Concrete Rev3 Witnesses Witnesses2 Witnesses3
  Witnesses4.
From Durable Require Rev3Counter.
Import ListNotations.
Open Scope string_scope.
(* The cases of one statement: each equality, or each equality of a conjunction. The
   expected side is marked when it is itself a run of an executor. *)
Ltac self_mark r := match r with
  | run _ _ _ _ _ => constr:(true) | run3 _ _ _ _ _ => constr:(true) | _ => constr:(false) end.
Ltac eqs_of name T := match T with
  | ?A /\ ?B =>
      let a := eqs_of name A in let b := eqs_of name B in constr:(List.app a b)
  | ?l = ?r => let s := self_mark r in constr:([(name, s, l, r)])
  end.
Ltac cases_of name th :=
  let T := type of th in
  let T' := eval cbv zeta in T in
  let cs := eqs_of name T' in exact cs.
EOF
  for t in $names; do
    id=$(printf '%s' "$t" | tr . _)
    echo "Definition c_$id : list (string * bool * list Action * list Action) :="
    echo "  ltac:(first [cases_of \"$t\" $t |"
    echo "               exact [(append \"SKIPPED \" \"$t\", false, [], [])]])."
  done
  echo "Definition cases : list (string * bool * list Action * list Action) :="
  echo "  List.concat ["
  printf '%s\n' $names | tr . _ | sed 's/^/  c_/; s/$/;/' | sed '$ s/;$//'
  echo "]."
  echo "Extraction Language OCaml."
  echo "From Coq Require Import ExtrOcamlBasic ExtrOcamlString."
  echo "Extraction \"durable_cases.ml\" cases."
} > "$work/Cases.v"

cat > "$work/main.ml" <<'EOF'
let name_of cs = String.of_seq (List.to_seq cs)
let () =
  let ok = ref 0 and self = ref 0 and bad = ref 0 and skipped = ref 0 in
  List.iter (fun (((n, is_self), computed), expected) ->
      let n = name_of n in
      if String.length n >= 8 && String.sub n 0 8 = "SKIPPED " then
        (incr skipped; Printf.printf "skip %s\n" n)
      else if computed <> expected then (incr bad; Printf.printf "MISMATCH %s\n" n)
      else if is_self then incr self
      else incr ok)
    Durable_cases.cases;
  Printf.printf "agree=%d self=%d mismatch=%d skipped=%d\n" !ok !self !bad !skipped;
  exit (if !bad = 0 then 0 else 1)
EOF

cd "$work" || fail "no work directory"
coqc -R "$here/Executor" Durable -R "$here/Scheduling" Scheduling Cases.v >coqc.log 2>&1 \
  || { cat coqc.log >&2; fail "extraction failed"; }

# build DIR: a native binary and a JavaScript file from the extracted code in DIR.
build() {
  ( cd "$1" &&
    ocamlfind ocamlopt -package str durable_cases.mli durable_cases.ml main.ml \
      -o check >ocaml.log 2>&1 &&
    ocamlfind ocamlc -package str durable_cases.mli durable_cases.ml main.ml \
      -o check.byte >>ocaml.log 2>&1 &&
    js_of_ocaml check.byte -o check.js >>ocaml.log 2>&1 ) \
    || { cat "$1/ocaml.log" >&2; fail "build failed in $1"; }
}

build .
native=$(./check); nstatus=$?
js=$(node --stack-size=$STACK check.js); jstatus=$?
echo "native: $(printf '%s\n' "$native" | tail -1)"
echo "javascript: $(printf '%s\n' "$js" | tail -1)"
printf '%s\n' "$native" | grep '^skip ' || true
[ "$nstatus" -eq 0 ] || fail "the native extracted executor disagrees with the kernel"
[ "$jstatus" -eq 0 ] || fail "the JavaScript extracted executor disagrees with the kernel"
[ "$native" = "$js" ] || fail "native and JavaScript results differ"
agreed=$(printf '%s\n' "$native" | sed -n 's/^agree=\([0-9]*\).*/\1/p')
[ -n "$agreed" ] && [ "$agreed" -eq "$EXPECTED" ] \
  || fail "${agreed:-0} cases agree, pinned count $EXPECTED"

mkdir mutant && cp durable_cases.mli main.ml mutant/ || fail "no mutant directory"
sed 's/^let cmd_eqb a b =$/let cmd_eqb _ _ = true\nlet _cmd_eqb_orig a b =/' durable_cases.ml \
  > mutant/durable_cases.ml
grep -q '^let cmd_eqb _ _ = true' mutant/durable_cases.ml || fail "mutant not applied"
build mutant
if ./mutant/check >mutant/native.out; then fail "native checker mutant passed"; fi
if node --stack-size=$STACK mutant/check.js >mutant/js.out; then
  fail "JavaScript checker mutant passed"; fi
for out in native js; do
  grep -q '^MISMATCH Witnesses.different_journal_mismatches' mutant/$out.out \
    || fail "$out checker mutant failed for the wrong reason"
done
echo "PASS: $agreed cases agree with the kernel, natively and in JavaScript; both checker mutants fail"
