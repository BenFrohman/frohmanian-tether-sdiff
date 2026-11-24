#!/usr/bin/env bash
# Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Benjamin Stanley Frohman
#
# Truth Gate verification (see TRUTH_GATE.md). Fails on: a skip or exclusion construct in the CI
# or scripts, sorry/admit/native_decide/axiom in ANY tracked .lean file, a `sorry` warning,
# sorryAx, ofReduceBool or error anywhere in any build log, a tracked .lean file that is not
# built, run by CI or a verified excerpt, a nonstandard axiom in any Scratch declaration, a
# missing or edited correspondence lock, a paper hash/quote mismatch, a failed lake build,
# nonstandard axioms in the locked theorems, a definitional (vacuous) correspondence, a
# correspondence proof that leans on the main theorem, or a paper_claim that reuses repository
# Props instead of transcribing the paper (lock-form lint). No file or directory is exempt.
#
# Every phase runs, even after an earlier one fails, so the final verdict can say exactly which
# kind of failure happened. scripts/truth_gate_classify.py then sorts each failure into one class
# (KERNEL/PROOF, LOCK-FORM, PAPER-HASH, STALE-BASE) and prints the TRUTH GATE VERDICT block.
# Only KERNEL/PROOF is ever described as a proof failure.
set -uo pipefail
cd "$(dirname "$0")/.."
mkdir -p truth-gate-report
: > truth-gate-report/phases.tsv
rm -f truth-gate-report/lint.json truth-gate-report/classification.json
phase() { printf '%s\t%s\n' "$1" "$2" >> truth-gate-report/phases.tsv; }

echo "== 1/9 no-skip guard (every line of every workflow and script)"
python3 scripts/check_no_skips.py > truth-gate-report/build-noskip.log 2>&1; rc=$?
cat truth-gate-report/build-noskip.log; phase build-noskip "$rc"

echo "== 2/9 static lock checks (lock form, paper hash, forbidden tokens in every tracked .lean file)"
python3 scripts/truth_gate_check.py > truth-gate-report/static.txt 2>&1; rc=$?
cat truth-gate-report/static.txt; phase static "$rc"

echo "== 3/9 lock-form lint (paper_claim must not reuse repository Props)"
python3 scripts/truth_gate_classify.py lint 2>&1 | tee truth-gate-report/lint.txt; phase lint "${PIPESTATUS[0]}"

MOD=$(python3 -c "import json;print(json.load(open('TRUTH_GATE.lock'))['semantics_module'])")
echo "== 4/9 lake build (default targets), lake build Scratch (every Scratch module)"
lake build 2>&1 | tee truth-gate-report/build.log; phase build "${PIPESTATUS[0]}"
lake build Scratch 2>&1 | tee truth-gate-report/build-scratch.log; phase build-scratch "${PIPESTATUS[0]}"
cat truth-gate-report/build-scratch.log >> truth-gate-report/build.log
if [ -n "$MOD" ]; then
  echo "== 5/9 lake build $MOD"
  lake build "$MOD" 2>&1 | tee truth-gate-report/build-semantics.log; phase build-semantics "${PIPESTATUS[0]}"
  cat truth-gate-report/build-semantics.log >> truth-gate-report/build.log
fi
echo "-- reading every line of the build log"
python3 scripts/check_build_log.py truth-gate-report/build.log > truth-gate-report/sorry.txt 2>&1; rc=$?
cat truth-gate-report/sorry.txt; phase sorry "$rc"
[ "$rc" -eq 0 ] && : > truth-gate-report/sorry.txt

echo "== 6/9 coverage: every tracked .lean file is built, run by CI, or a verified excerpt of a built file"
python3 scripts/check_lean_coverage.py > truth-gate-report/build-coverage.log 2>&1; rc=$?
cat truth-gate-report/build-coverage.log; phase build-coverage "$rc"

echo "== 7/9 kernel audit of the lock (axioms, non-vacuity, transport)"
lake env lean scripts/TruthGateAudit.lean > truth-gate-report/audit.txt 2>&1
cat truth-gate-report/audit.txt
if grep -q 'TRUTH GATE AUDIT PASS' truth-gate-report/audit.txt && ! grep -qE 'TRUTH GATE FAIL|error:|sorryAx' truth-gate-report/audit.txt; then
  phase audit 0; else phase audit 1; fi

echo "== 8/9 additional locks (build, sorry scan of every log line, kernel audit)"
python3 - <<'PY2' > truth-gate-report/additional.txt
import json
for ex in json.load(open("TRUTH_GATE.lock")).get("additional_locks", []):
    print(ex["semantics_module"], ex["audit_file"])
PY2
i=0
while read -r XMOD XAUDIT; do
  [ -n "$XMOD" ] || continue
  i=$((i+1))
  echo "-- lake build $XMOD"
  lake build "$XMOD" > "truth-gate-report/build-additional-$i.log" 2>&1; brc=$?
  cat "truth-gate-report/build-additional-$i.log"; phase "build-additional-$i" "$brc"
  python3 scripts/check_build_log.py "truth-gate-report/build-additional-$i.log" > "truth-gate-report/sorry-additional-$i.txt" 2>&1; src=$?
  cat "truth-gate-report/sorry-additional-$i.txt"; phase "sorry-additional-$i" "$src"
  [ "$src" -eq 0 ] && : > "truth-gate-report/sorry-additional-$i.txt"
  echo "-- kernel audit $XAUDIT"
  lake env lean "$XAUDIT" > "truth-gate-report/audit-additional-$i.txt" 2>&1
  cat "truth-gate-report/audit-additional-$i.txt"
  if grep -q 'TRUTH GATE AUDIT PASS' "truth-gate-report/audit-additional-$i.txt" && ! grep -qE 'TRUTH GATE FAIL|error:|sorryAx' "truth-gate-report/audit-additional-$i.txt"; then
    phase "audit-additional-$i" 0; else phase "audit-additional-$i" 1; fi
done < truth-gate-report/additional.txt
[ "$i" -gt 0 ] || echo "(none)"

echo "== 9/9 axioms of every Scratch declaration"
lake env lean scripts/ScratchAxiomAuditAll.lean > truth-gate-report/build-scratch-axioms.log 2>&1; arc=$?
cat truth-gate-report/build-scratch-axioms.log
if [ "$arc" -eq 0 ] && grep -q '^SCRATCH FULL AUDIT PASS' truth-gate-report/build-scratch-axioms.log \
   && python3 scripts/check_build_log.py truth-gate-report/build-scratch-axioms.log; then
  phase build-scratch-axioms 0; else phase build-scratch-axioms 1; fi

SEMF=$(python3 -c "import json;print(json.load(open('TRUTH_GATE.lock'))['semantics_file'])")
sha256sum TRUTH_GATE.lock "$SEMF" > truth-gate-report/sha256.txt
python3 scripts/truth_gate_classify.py report; rc=$?
if [ "$rc" -eq 0 ]; then
  echo "TRUTH GATE PASS at $(git rev-parse HEAD 2>/dev/null || echo unknown)"
fi
exit "$rc"
