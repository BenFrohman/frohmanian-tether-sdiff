#!/usr/bin/env bash
# Copyright (c) 2026 Benjamin Stanley Frohman. Apache-2.0.
# Collect a real lake-build / certificate-attempt bundle from this repository
# checkout. Safe after a passing, failing, or partial run. Never invents
# elan/lake/lean versions: if a tool is missing, that fact is written down.
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
OUT="${1:-cert-bundle}"
mkdir -p "$OUT"

write_missing() {
  local label="$1"
  printf 'MISSING: %s\n' "$label" > "$OUT/$2"
}

if git rev-parse HEAD >/dev/null 2>&1; then
  git rev-parse HEAD > "$OUT/commit.txt"
else
  write_missing "git commit SHA was not available in this checkout" "commit.txt"
fi

if [ -f lake-manifest.json ]; then
  cp -a lake-manifest.json "$OUT/lake-manifest.json"
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum lake-manifest.json | awk '{print $1}' > "$OUT/lake-manifest.json.sha256"
    sha256sum lake-manifest.json > "$OUT/lake-manifest.json.sha256sum"
  else
    python3 -c "import hashlib,pathlib; p=pathlib.Path('lake-manifest.json'); h=hashlib.sha256(p.read_bytes()).hexdigest(); pathlib.Path('$OUT/lake-manifest.json.sha256').write_text(h+'\n'); pathlib.Path('$OUT/lake-manifest.json.sha256sum').write_text(h+'  lake-manifest.json\n')"
  fi
else
  write_missing "lake-manifest.json was not present in the checkout" "MISSING-lake-manifest.txt"
fi

if [ -f lean-toolchain ]; then
  cp -a lean-toolchain "$OUT/lean-toolchain"
else
  write_missing "lean-toolchain was not present in the checkout" "MISSING-lean-toolchain.txt"
fi

{
  echo "commit: $(git rev-parse HEAD 2>/dev/null || echo 'not available')"
  echo "github_sha: ${GITHUB_SHA:-not set in environment}"
  echo "github_run_id: ${GITHUB_RUN_ID:-not set in environment}"
  echo "github_run_attempt: ${GITHUB_RUN_ATTEMPT:-not set in environment}"
  echo "github_event_name: ${GITHUB_EVENT_NAME:-not set in environment}"
  echo "github_repository: ${GITHUB_REPOSITORY:-not set in environment}"
  if command -v elan >/dev/null 2>&1; then
    echo "elan --version:"
    elan --version
  else
    echo "elan --version: not printed; elan was not on PATH"
  fi
  if command -v lake >/dev/null 2>&1; then
    echo "lake --version:"
    lake --version
  else
    echo "lake --version: not printed; lake was not on PATH"
  fi
  if command -v lean >/dev/null 2>&1; then
    echo "lean --version:"
    lean --version
  else
    echo "lean --version: not printed; lean was not on PATH"
  fi
} > "$OUT/versions.txt" 2>&1

python3 - "$OUT" <<'PY'
import json, pathlib, sys
out = pathlib.Path(sys.argv[1])
dest = out / "mathlib-rev.txt"
manifest = pathlib.Path("lake-manifest.json")
if not manifest.exists():
    dest.write_text("Mathlib rev: not available; lake-manifest.json missing\n")
    raise SystemExit(0)
try:
    data = json.loads(manifest.read_text())
except Exception as e:
    dest.write_text(f"Mathlib rev: could not parse lake-manifest.json ({e})\n")
    raise SystemExit(0)
found = False
lines = []
for pkg in data.get("packages") or []:
    if pkg.get("name") == "mathlib":
        lines.append("name: mathlib")
        lines.append(f"rev: {pkg.get('rev')}")
        lines.append(f"inputRev: {pkg.get('inputRev')}")
        lines.append(f"url: {pkg.get('url')}")
        found = True
        break
if not found:
    lines.append("Mathlib rev: no package named mathlib in lake-manifest.json")
dest.write_text("\n".join(lines) + "\n")
PY

# Hash every file currently in the bundle and write README last.
python3 - "$OUT" <<'PY'
import hashlib, pathlib, sys, os
out = pathlib.Path(sys.argv[1])
rows = []
for p in sorted(out.iterdir()):
    if p.name in ("README.md", "SHA256SUMS") or not p.is_file():
        continue
    h = hashlib.sha256(p.read_bytes()).hexdigest()
    rows.append((h, p.stat().st_size, p.name))
sha_lines = [f"{h}  {name}" for h, _, name in rows]
(out / "SHA256SUMS").write_text("\n".join(sha_lines) + ("\n" if sha_lines else ""))
readme = []
readme.append("# Lake certificate bundle")
readme.append("")
readme.append("This directory is a real Lean lake-build / kernel-certificate attempt")
readme.append("from this repository's own committed lake-manifest.json.")
readme.append("A hand-written CI_RUN summary is not a certificate.")
readme.append("Third-party or dummy checkers do not prove or pass anything;")
readme.append("the final pass, if any, rests only on the Lean kernel and #print axioms.")
readme.append("")
if (out / "commit.txt").exists():
    readme.append(f"Commit: {(out / 'commit.txt').read_text().strip()}")
if os.environ.get("GITHUB_RUN_ID"):
    repo = os.environ.get("GITHUB_REPOSITORY", "")
    run = os.environ["GITHUB_RUN_ID"]
    readme.append(f"GitHub Actions run: {run}")
    if repo:
        readme.append(f"Run URL: https://github.com/{repo}/actions/runs/{run}")
readme.append("")
readme.append("File SHA-256 checksums:")
readme.append("")
readme.append("```")
readme.extend(f"{h}  {name}  ({size} bytes)" for h, size, name in rows)
readme.append("```")
readme.append("")
missing = [p.name for p in sorted(out.iterdir()) if p.name.startswith("MISSING-")]
expected = [
    "lake-manifest.json",
    "lake-manifest.json.sha256",
    "lean-toolchain",
    "versions.txt",
    "mathlib-rev.txt",
    "commit.txt",
    "lake-build.log",
]
present = {p.name for p in out.iterdir() if p.is_file()}
# print-axioms outputs have repo-specific names; noted if any axiom/print logs exist
axiomish = sorted(n for n in present if any(k in n.lower() for k in ("axiom", "print-axiom", "print_axiom")))
if "lake-build.log" not in present:
    readme.append("Note: lake-build.log is not in this bundle yet (the build log is teed by the workflow step).")
    readme.append("")
if not axiomish:
    readme.append("Note: #print axioms output is not in this bundle yet, or the axiom step did not run.")
    readme.append("")
if missing:
    readme.append("Missing inputs recorded in: " + ", ".join(missing))
    readme.append("")
(out / "README.md").write_text("\n".join(readme) + "\n")
PY
