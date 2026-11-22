#!/usr/bin/env bash
# Proof gate for a Coq (Rocq) project built with coq_makefile. Run it from the project root.
# The Coq counterpart of check-axioms.sh, with the same four checks.
#
# Usage: check-axioms-coq.sh <coqproject> <committed-report> <theorem-list> [<allowed-assumptions>]
# Example: check-axioms-coq.sh _CoqProject axioms-report.txt theorems.txt
#
# <coqproject> is the _CoqProject file. Its "-R <dir> <logical>" lines map directories to logical
# names, and its .v lines are the project's modules. <theorem-list> holds one fully qualified
# name per line (for example Scheduling.Replay.replay_determinism); blank lines and lines starting
# with # are ignored. It must name exactly the theorems written in the project's modules, which
# the gate reads back from Coq with Search, so a theorem left out of both the list and the report
# still fails. <allowed-assumptions>, if given, names the assumptions any constant may use, one
# per line, as Print Assumptions prints them; without it no constant may use any assumption.
# Exits 0 only if every check passes, 1 if a check fails and 2 on bad usage.
#
# The assumption audit (check 4) reads every constant each module declares, definitions and
# inductives included, not only the listed theorems, and fails on any assumption outside the
# allowed set. That catches a Hypothesis or Variable outside a section, which Coq turns into an
# axiom, wherever it is used. Its blind spots: constants a module declares through a plugin that
# Search does not list, and assumptions Print Assumptions does not report. Output it cannot parse
# fails the gate. The locale is pinned, so sorting and comparison do not depend on the caller's.
#
# Checked on Coq 8.20.1. Coq lists no Admitted theorem under any Search kind, so the source scan
# and the Print Assumptions report are what catch one. Search kinds that a later version renames
# make the inventory check fail rather than pass. The source scan is crude: it also matches
# comments, which errs on the safe side.

set -euo pipefail
export LC_ALL=C

if [ $# -ne 3 ] && [ $# -ne 4 ]; then
  echo "Usage: $0 <coqproject> <committed-report> <theorem-list> [<allowed-assumptions>]" >&2
  exit 2
fi
PROJECT=$1 REPORT=$2 THEOREMS=$3 ALLOWED=${4:-}
for f in "$PROJECT" "$THEOREMS" ${ALLOWED:+"$ALLOWED"}; do
  [ -f "$f" ] || { echo "missing file: $f" >&2; exit 2; }
done
WORK=$(mktemp -d)
# coq_makefile writes only into the current directory, so its output goes here and is removed.
MK=.check-axioms-coq.mk
trap 'rm -rf "$WORK"; rm -f "$MK" "$MK.conf" ".$MK.d"' EXIT

fail() { echo "FAIL: $*" >&2; exit 1; }

# The theorem kinds Coq's Search accepts. Every kind is queried, so a theorem declared with any
# of these keywords is in the inventory.
KINDS="Theorem Lemma Fact Remark Property Proposition Corollary"
# Declarations that add an assumption without a proof, and commands that switch off a kernel
# check. A conservative text scan: it also matches comments and strings, never misses these
# spellings, and check 4 covers what it cannot see.
FORBIDDEN='\b(Admitted|admit|Axiom|Axioms|Parameter|Parameters|Conjecture|bypass_check)\b|Unset[[:space:]]+(Guard|Positivity|Universe)[[:space:]]+Checking'

# The project's modules, as file paths and as logical names.
FILES=()
while IFS= read -r line; do FILES+=("$line"); done < <(grep -E '^[^-#[:space:]].*\.v[[:space:]]*$' "$PROJECT" | sed 's/[[:space:]]*$//')
[ "${#FILES[@]}" -gt 0 ] || fail "no .v files listed in $PROJECT"
logical_name() {
  local file=$1 dir name
  while read -r flag dir name; do
    [ "$flag" = "-R" ] || [ "$flag" = "-Q" ] || continue
    dir=${dir%/}
    case $file in
      "$dir"/*) local rest=${file#"$dir"/}; rest=${rest%.v}; echo "$name.${rest//\//.}"; return 0 ;;
    esac
  done < "$PROJECT"
  return 1
}
MODULES=()
for file in "${FILES[@]}"; do
  [ -f "$file" ] || fail "listed module does not exist: $file"
  module=$(logical_name "$file") || fail "no -R or -Q mapping covers $file"
  MODULES+=("$module")
done

# 1. No assumption without a proof in the sources.
status=0
grep -nE "$FORBIDDEN" "${FILES[@]}" > "$WORK/forbidden" || status=$?
[ "$status" -le 1 ] || fail "source scan could not read the sources"
[ "$status" -eq 1 ] || { cat "$WORK/forbidden" >&2; fail "sources contain an unproved assumption or a disabled kernel check (listed above)"; }

# 2. Clean build.
rm -f "${FILES[@]/%/o}" "${FILES[@]/%/ok}" "${FILES[@]/%/os}" "${FILES[@]/%/.glob}"
coq_makefile -f "$PROJECT" -o "$MK" > "$WORK/coq_makefile.log" 2>&1 \
  || { cat "$WORK/coq_makefile.log" >&2; fail "coq_makefile failed"; }
make -f "$MK" > "$WORK/build.log" 2>&1 || { cat "$WORK/build.log" >&2; fail "build failed"; }

# 3. Inventory: the theorems Coq reports in the project's modules equal the theorem list.
# Each module is queried in its own run with Require Import, so Search prints short names, which
# the gate then qualifies with that module's logical name.
FLAGS=$(grep -E '^-[RQ] ' "$PROJECT" | tr '\n' ' ')
: > "$WORK/found"
for module in "${MODULES[@]}"; do
  {
    echo "Require Import $module."
    for kind in $KINDS; do echo "Search is:$kind inside $module."; done
  } > "$WORK/Inventory.v"
  coqc -q $FLAGS "$WORK/Inventory.v" > "$WORK/inventory.out" 2>&1 \
    || { cat "$WORK/inventory.out" >&2; fail "inventory query failed for $module"; }
  # Search prints "name: type", with types that may continue on indented lines.
  { grep -E '^[A-Za-z_][A-Za-z0-9_'"'"']*:' "$WORK/inventory.out" || true; } \
    | sed "s/:.*//; s/^/$module./" >> "$WORK/found"
done
sort -u -o "$WORK/found" "$WORK/found"
{ grep -vE '^[[:space:]]*(#|$)' "$THEOREMS" || true; } | sed 's/[[:space:]]*$//' | sort -u > "$WORK/listed"
[ -s "$WORK/found" ] || fail "no theorems found in the project's modules"
if ! diff -u "$WORK/listed" "$WORK/found" > "$WORK/inventory.diff"; then
  cat "$WORK/inventory.diff" >&2
  fail "theorem list differs from the theorems in the sources (- listed only, + sources only)"
fi

# 4. Assumption audit: every constant every module declares uses only allowed assumptions.
# Search under a plain Require prints each name in a form that resolves in the same context, so
# the names are queried with Print Assumptions under the same Requires.
REQUIRES=$(for module in "${MODULES[@]}"; do echo "Require $module."; done)
: > "$WORK/constants"
for module in "${MODULES[@]}"; do
  echo "$REQUIRES
Search _ inside $module." > "$WORK/One.v"
  coqc -q $FLAGS "$WORK/One.v" > "$WORK/one.out" 2>&1 \
    || { cat "$WORK/one.out" >&2; fail "constant inventory query failed for $module"; }
  count=0
  while IFS= read -r name; do echo "$name" >> "$WORK/constants"; count=$((count + 1)); done \
    < <(grep -E "^[A-Za-z_][A-Za-z0-9_'.]*:" "$WORK/one.out" | sed 's/:.*//')
  [ "$count" -gt 0 ] || fail "module $module declares no constant the audit can see"
done
constants=$(wc -l < "$WORK/constants" | tr -d ' ')
[ "$constants" -ge "$(wc -l < "$WORK/listed" | tr -d ' ')" ] \
  || fail "assumption audit saw $constants constants, fewer than the listed theorems"
{ echo "$REQUIRES"; while read -r name; do echo "Print Assumptions $name."; done < "$WORK/constants"; } \
  > "$WORK/Audit.v"
coqc -q $FLAGS "$WORK/Audit.v" > "$WORK/audit.out" 2>&1 \
  || { cat "$WORK/audit.out" >&2; fail "Print Assumptions failed in the assumption audit"; }
{ [ -n "$ALLOWED" ] && grep -vE '^[[:space:]]*(#|$)' "$ALLOWED" | sed 's/[[:space:]]*$//' || true; } \
  | sort -u > "$WORK/allowed"
# Each constant's block is "Closed under the global context", or "Axioms:" followed by lines
# "name : type", with types continuing on indented lines, or by lines such as "f is assumed to
# be guarded." for a switched-off kernel check. Anything else fails closed.
awk -v names="$WORK/constants" -v allowed="$WORK/allowed" '
  BEGIN { while ((getline n < names) > 0) list[++count] = n
          while ((getline a < allowed) > 0) ok[a] = 1; i = 0; bad = 0 }
  /^Closed under the global context$/ { i++; inaxioms = 0; next }
  /^Axioms:$/ { i++; inaxioms = 1; next }
  /^[[:space:]]/ && inaxioms { next }
  inaxioms && / is assumed to be / { if (!($0 in ok)) { print "FAIL: " list[i] " uses " $0 > "/dev/stderr"; bad = 1 }
                                     next }
  inaxioms && / : / { a = $0; sub(/ : .*/, "", a)
                      if (!(a in ok)) { print "FAIL: " list[i] " uses " a > "/dev/stderr"; bad = 1 }
                      next }
  { print "FAIL: unrecognised Print Assumptions output: " $0 > "/dev/stderr"; bad = 2 }
  END { if (i != count) { print "FAIL: audit read " i " blocks for " count " constants" > "/dev/stderr"; bad = 2 }
        exit bad }' "$WORK/audit.out" || fail "assumption audit: a constant uses an assumption outside the allowed set, or the output was not understood (listed above)"

# 5. Regenerate the axioms report and compare it with the committed one.
{
  for module in "${MODULES[@]}"; do echo "Require $module."; done
  while read -r name; do echo "Print Assumptions $name."; done < "$WORK/listed"
} > "$WORK/Axioms.v"
coqc -q $(grep -E '^-[RQ] ' "$PROJECT" | tr '\n' ' ') "$WORK/Axioms.v" > "$WORK/axioms.raw" 2>&1 \
  || { cat "$WORK/axioms.raw" >&2; fail "Print Assumptions failed"; }
# Label each theorem's section so the report says which theorem uses which axiom.
awk -v names="$WORK/listed" 'BEGIN { while ((getline n < names) > 0) list[++count] = n; i = 0 }
  /^Closed under the global context$/ || /^Axioms:$/ { i++; print "== " list[i] }
  { print }' "$WORK/axioms.raw" > "$WORK/report"
sections=$(grep -c '^== ' "$WORK/report" || true)
[ "$sections" -eq "$(wc -l < "$WORK/listed" | tr -d ' ')" ] || fail "axioms report does not cover every listed theorem"
[ -f "$REPORT" ] || { cp "$WORK/report" "$REPORT.new"; fail "no committed report; wrote $REPORT.new for review"; }
if ! diff -u "$REPORT" "$WORK/report" > "$WORK/report.diff"; then
  cat "$WORK/report.diff" >&2
  cp "$WORK/report" "$REPORT.new"
  fail "axioms report differs from the committed one; the new report is in $REPORT.new"
fi

echo "PASS: ${#MODULES[@]} modules, $(wc -l < "$WORK/listed" | tr -d ' ') theorems, $constants constants audited, axioms report unchanged"
