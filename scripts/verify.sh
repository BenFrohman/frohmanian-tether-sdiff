#!/usr/bin/env bash
# One-command reproducible verification, from a fresh clone:
#   bash scripts/verify.sh        (or: make verify)
# 1. installs elan if missing; elan reads the pinned toolchain from `lean-toolchain`
# 2. fetches the prebuilt Mathlib cache for the rev pinned in `lake-manifest.json`
# 3. builds the library, scans the sources for sorry/admit/native_decide/axiom,
#    runs the strict axiom audit, and prints `#print axioms` for the headline theorems.
set -euo pipefail
cd "$(dirname "$0")/.."

if ! command -v lake >/dev/null 2>&1; then
  if [ ! -x "$HOME/.elan/bin/lake" ]; then
    echo "== installing elan (toolchain from lean-toolchain: $(cat lean-toolchain))"
    curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --default-toolchain none
  fi
  export PATH="$HOME/.elan/bin:$PATH"
fi

echo "== commit: $(git rev-parse HEAD 2>/dev/null || echo unknown)"
echo "== toolchain: $(cat lean-toolchain)"
echo "== mathlib rev (lake-manifest.json): $(python3 -c 'import json;print(next(p["rev"] for p in json.load(open("lake-manifest.json"))["packages"] if p["name"]=="mathlib"))')"
lake --version

echo "== fetching Mathlib cache"
lake exe cache get

echo "== lake build"
lake build

echo "== source scan"
python3 scripts/check_no_sorry.py

echo "== strict axiom audit"
lake env lean scripts/AxiomAudit.lean 2>&1 | tee axioms.txt
grep -q "^AUDIT PASS" axioms.txt
if grep -v "^AUDIT PASS" axioms.txt | grep -qE "AUDIT FAIL|sorryAx|ofReduceBool|error"; then
  echo "AXIOM AUDIT FAILED"; exit 1
fi
grep "^AUDIT SUMMARY" axioms.txt

echo "== #print axioms (headline theorems)"
lake env lean scripts/PrintAxioms.lean 2>&1 | tee print_axioms.txt
if grep -qE "sorryAx|ofReduceBool|error" print_axioms.txt; then
  echo "HEADLINE AXIOMS FAILED"; exit 1
fi

echo "VERIFY OK"
