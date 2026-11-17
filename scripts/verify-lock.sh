#!/usr/bin/env bash
# Author: Benjamin Stanley Frohman
# Truth Gate verification (see TRUTH_GATE.md). Fails on: sorry/admit/native_decide/axiom in ANY
# tracked .lean file, a `sorry` warning anywhere in any build log, a .lean file that is not built
# or scanned, a skip/exclusion construct in the CI or scripts, a missing or edited correspondence
# lock, a paper hash/quote mismatch, a failed lake build, nonstandard axioms in the locked
# theorems, a definitional (vacuous) correspondence, or a correspondence proof that leans on the
# main theorem. No file or directory is exempt.
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p truth-gate-report
echo "== 1/7 no-skip guard (CI and scripts)"
python3 scripts/check_no_skips.py | tee truth-gate-report/no-skips.txt
echo "== 2/7 static checks (every tracked .lean file)"
python3 scripts/truth_gate_check.py | tee truth-gate-report/static.txt
MOD=$(python3 -c "import json;print(json.load(open('TRUTH_GATE.lock'))['semantics_module'])")
echo "== 3/7 lake build (default targets), lake build Scratch, lake build $MOD"
lake build 2>&1 | tee truth-gate-report/build.log
lake build Scratch 2>&1 | tee -a truth-gate-report/build.log
lake build "$MOD" 2>&1 | tee -a truth-gate-report/build.log
python3 scripts/check_build_log.py truth-gate-report/build.log
echo "== 4/7 coverage: every tracked .lean file is built, run by CI, or a verbatim excerpt of a built file"
python3 scripts/check_lean_coverage.py | tee truth-gate-report/coverage.txt
echo "== 5/7 kernel audit of the lock (axioms, non-vacuity, transport)"
lake env lean scripts/TruthGateAudit.lean 2>&1 | tee truth-gate-report/audit.txt
grep -q 'TRUTH GATE AUDIT PASS' truth-gate-report/audit.txt
if grep -qE 'TRUTH GATE FAIL|error:|sorryAx' truth-gate-report/audit.txt; then exit 1; fi
echo "== 6/7 additional locks (build, sorry scan, kernel audit)"
python3 - <<'PY2' > truth-gate-report/additional.txt
import json
for ex in json.load(open("TRUTH_GATE.lock")).get("additional_locks", []):
    print(ex["semantics_module"], ex["audit_file"])
PY2
while read -r XMOD XAUDIT; do
  [ -n "$XMOD" ] || continue
  echo "-- lake build $XMOD"
  lake build "$XMOD" 2>&1 | tee truth-gate-report/build-additional.log
  python3 scripts/check_build_log.py truth-gate-report/build-additional.log
  echo "-- kernel audit $XAUDIT"
  lake env lean "$XAUDIT" 2>&1 | tee truth-gate-report/audit-additional.txt
  grep -q 'TRUTH GATE AUDIT PASS' truth-gate-report/audit-additional.txt
  if grep -qE 'TRUTH GATE FAIL|error:|sorryAx' truth-gate-report/audit-additional.txt; then exit 1; fi
done < truth-gate-report/additional.txt
echo "== 7/7 full axiom audit of every Scratch declaration"
lake env lean scripts/ScratchAxiomAuditAll.lean 2>&1 | tee truth-gate-report/scratch-axioms-all.txt
python3 scripts/check_build_log.py truth-gate-report/scratch-axioms-all.txt
grep -q '^SCRATCH FULL AUDIT PASS' truth-gate-report/scratch-axioms-all.txt
sha256sum TRUTH_GATE.lock "$(python3 -c "import json;print(json.load(open('TRUTH_GATE.lock'))['semantics_file'])")" > truth-gate-report/sha256.txt
echo "TRUTH GATE PASS at $(git rev-parse HEAD 2>/dev/null || echo unknown)"
