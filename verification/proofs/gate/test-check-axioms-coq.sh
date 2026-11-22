#!/usr/bin/env bash
# Tests for check-axioms-coq.sh, following the gate-integrity standard block. Each fixture is a
# small Coq project built in a temporary directory; each case asserts PASS or the named FAIL
# message. Requires coqc and coq_makefile on PATH. Exits 0 only if every case behaves as stated.
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
GATE="$HERE/check-axioms-coq.sh"
ROOT=$(mktemp -d)
trap 'rm -rf "$ROOT"' EXIT
failures=0

# fixture <name> <coq source> <theorem list>: a project with module Fix.Main.
fixture() {
  local dir="$ROOT/$1"
  mkdir -p "$dir/Fix"
  printf '%s\n' "$2" > "$dir/Fix/Main.v"
  printf -- '-R Fix Fix\nFix/Main.v\n' > "$dir/_CoqProject"
  printf '%s\n' "$3" > "$dir/theorems.txt"
  printf 'Classical_Prop.classic\n' > "$dir/allowed.txt"
  echo "$dir"
}
# expect <case> <dir> <PASS|substring of FAIL> [gate] [allowed file, or - for none]
expect() {
  local name=$1 dir=$2 want=$3 gate=${4:-$GATE} allowed=${5:-allowed.txt} out status
  [ "$allowed" = - ] && allowed=
  out=$(cd "$dir" && "$gate" _CoqProject axioms-report.txt theorems.txt $allowed 2>&1); status=$?
  if [ "$want" = PASS ]; then
    if [ $status -eq 0 ] && echo "$out" | grep -q '^PASS:'; then echo "ok   $name"; return; fi
  elif [ $status -eq 1 ] && echo "$out" | grep -qF "$want"; then echo "ok   $name"; return; fi
  echo "FAIL $name: wanted '$want', got status $status:"; echo "$out" | tail -5 | sed 's/^/     /'
  failures=$((failures + 1))
}
# accept <dir>: commit the report the gate proposed, as a reviewer would.
accept() { mv "$1/axioms-report.txt.new" "$1/axioms-report.txt"; }

CLEAN='Require Import Coq.Logic.Classical_Prop.
Theorem t_ok : 1 + 1 = 2. Proof. reflexivity. Qed.
Lemma l_classical : forall P : Prop, P \/ ~ P. Proof. intro P. apply classic. Qed.
Corollary c_kind : 2 + 2 = 4. Proof. reflexivity. Qed.
Definition not_a_theorem := 5.'
LIST='Fix.Main.t_ok
Fix.Main.l_classical
Fix.Main.c_kind'

d=$(fixture clean "$CLEAN" "$LIST")
expect "clean project without a committed report" "$d" "no committed report"
accept "$d"
expect "clean project, report committed" "$d" PASS
grep -q 'Classical_Prop.classic' "$d/axioms-report.txt" && echo "ok   report names the classical axiom" \
  || { echo "FAIL report names the classical axiom"; failures=$((failures + 1)); }
grep -q 'Closed under the global context' "$d/axioms-report.txt" && echo "ok   report marks a closed theorem" \
  || { echo "FAIL report marks a closed theorem"; failures=$((failures + 1)); }

d=$(fixture admitted "$CLEAN
Theorem t_admitted : 2 + 2 = 5. Proof. Admitted." "$LIST")
expect "Admitted proof" "$d" "unproved assumption"

d=$(fixture axiom "$CLEAN
Axiom my_axiom : False." "$LIST")
expect "Axiom declaration" "$d" "unproved assumption"

d=$(fixture comment "$CLEAN
(* this proof is not Admitted *)" "$LIST")
expect "watch word in a comment fails (conservative scan)" "$d" "unproved assumption"

d=$(fixture unlisted "$CLEAN
Theorem t_extra : 3 = 3. Proof. reflexivity. Qed." "$LIST")
expect "theorem in the sources but not the list" "$d" "theorem list differs"

d=$(fixture absent "$CLEAN" "$LIST
Fix.Main.t_missing")
expect "theorem in the list but not the sources" "$d" "theorem list differs"

d=$(fixture stale "$CLEAN" "$LIST")
expect "stale: first run" "$d" "no committed report"; accept "$d"
sed -i '' 's/Proof. reflexivity. Qed./Proof. apply NNPP. intro H. apply H. reflexivity. Qed./' "$d/Fix/Main.v"
expect "proof now uses another axiom" "$d" "axioms report differs"

d=$(fixture broken "Theorem t_bad : 1 = 1. Proof. reflexivity" "Fix.Main.t_bad")
expect "file that does not compile" "$d" "build failed"

d=$(fixture empty "Definition only := 1." "")
expect "project with no theorems" "$d" "no theorems found"

# Checker mutant: without the inventory comparison, the unlisted-theorem case must pass, which
# shows that case fails for its own reason.
MUTANT="$ROOT/mutant-gate.sh"
sed 's/if ! diff -u "\$WORK\/listed" "\$WORK\/found"/if false \&\& ! diff -u "$WORK\/listed" "$WORK\/found"/' "$GATE" > "$MUTANT"
chmod +x "$MUTANT"
grep -q 'if false && ! diff -u "\$WORK/listed"' "$MUTANT" || { echo "FAIL mutant was not applied"; failures=$((failures + 1)); }
d=$(fixture mutant "$CLEAN
Theorem t_extra : 3 = 3. Proof. reflexivity. Qed." "$LIST")
out=$(cd "$d" && "$MUTANT" _CoqProject axioms-report.txt theorems.txt allowed.txt 2>&1); status=$?
if [ $status -eq 0 ] || echo "$out" | grep -q "no committed report"; then
  echo "ok   checker mutant lets the unlisted theorem through"
else
  echo "FAIL checker mutant: expected it to miss the unlisted theorem, got: $(echo "$out" | tail -2)"
  failures=$((failures + 1))
fi

# The assumption audit. A Hypothesis outside a section is an axiom; a Definition that uses it is
# not a theorem, so only the audit sees it.
HYP='Set Warnings "-declaration-outside-section".
Hypothesis review_false : False.
Definition unchecked_proof : False := review_false.'
d=$(fixture hypothesis "$CLEAN
$HYP" "$LIST")
expect "module-level hypothesis used by a definition" "$d" "uses Main.review_false"
d=$(fixture hypothesis_removed "$CLEAN
Definition checked_proof : True := I." "$LIST")
expect "case mutant: the same definition without the hypothesis" "$d" "no committed report"
d=$(fixture no_allowed "$CLEAN" "$LIST")
expect "classical lemma with no allowed assumptions" "$d" "uses Classical_Prop.classic" "$GATE" -
d=$(fixture guard "$CLEAN
Unset Guard Checking.
Fixpoint loop (n : nat) : False := loop n." "$LIST")
expect "kernel guard check switched off" "$d" "disabled kernel check"

# The same switch split across lines escapes the line-based scan; the audit must catch it.
d=$(fixture guard_split "$CLEAN
Unset
  Guard Checking.
Fixpoint loop (n : nat) : False := loop n." "$LIST")
expect "kernel guard check switched off across lines" "$d" "loop is assumed to be guarded"

# A module that declares nothing the audit can see.
d=$(fixture empty_module "$CLEAN" "$LIST")
printf '(* nothing here *)\n' > "$d/Fix/Empty.v"
printf 'Fix/Empty.v\n' >> "$d/_CoqProject"
expect "module with no constants" "$d" "declares no constant"

# The locale. Zb and ab sort one way under C (uppercase first) and the other under en_US (case
# ignored), so a report written under one locale must still pass under the other.
LOCALE='Theorem ab : 1 = 1. Proof. reflexivity. Qed.
Theorem Zb : 2 = 2. Proof. reflexivity. Qed.'
LOCALE_LIST='Fix.Main.ab
Fix.Main.Zb'
locale_case() {
  local name=$1 gate=$2 want=$3 d out status
  d=$(fixture "locale_$name" "$LOCALE" "$LOCALE_LIST")
  (cd "$d" && LC_ALL=en_US.UTF-8 "$gate" _CoqProject axioms-report.txt theorems.txt > /dev/null 2>&1)
  accept "$d"
  out=$(cd "$d" && LC_ALL=C.UTF-8 "$gate" _CoqProject axioms-report.txt theorems.txt 2>&1); status=$?
  if { [ "$want" = PASS ] && [ $status -eq 0 ]; } || { [ "$want" = FAIL ] && [ $status -ne 0 ]; }; then
    echo "ok   $name"
  else
    echo "FAIL $name: wanted $want, got status $status: $(echo "$out" | tail -1)"
    failures=$((failures + 1))
  fi
}
locale_case "report written under en_US passes under C" "$GATE" PASS

# Checker mutants for the new checks.
AUDIT_MUTANT="$ROOT/audit-mutant-gate.sh"
sed 's/|| fail "assumption audit:/|| true "assumption audit:/' "$GATE" > "$AUDIT_MUTANT"
chmod +x "$AUDIT_MUTANT"
grep -q '|| true "assumption audit:' "$AUDIT_MUTANT" || { echo "FAIL audit mutant was not applied"; failures=$((failures + 1)); }
d=$(fixture hypothesis_mutant "$CLEAN
$HYP" "$LIST")
expect "checker mutant without the audit misses the hypothesis" "$d" "no committed report" "$AUDIT_MUTANT"
LOCALE_MUTANT="$ROOT/locale-mutant-gate.sh"
grep -v '^export LC_ALL=C$' "$GATE" > "$LOCALE_MUTANT"
chmod +x "$LOCALE_MUTANT"
grep -q '^export LC_ALL=C$' "$LOCALE_MUTANT" && { echo "FAIL locale mutant was not applied"; failures=$((failures + 1)); }
locale_case "checker mutant without the pinned locale fails across locales" "$LOCALE_MUTANT" FAIL

echo "$failures failure(s)"
[ $failures -eq 0 ]
