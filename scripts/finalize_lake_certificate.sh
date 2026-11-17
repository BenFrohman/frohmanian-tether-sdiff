#!/usr/bin/env bash
# Copyright (c) 2026 Benjamin Stanley Frohman. Apache-2.0.
# Recompute SHA256SUMS and README for an already-populated cert-bundle directory.
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
OUT="${1:-cert-bundle}"
if [ ! -d "$OUT" ]; then
  # allow a path relative to repo root
  if [ -d "$ROOT/$OUT" ]; then OUT="$ROOT/$OUT"; else
    echo "finalize_lake_certificate.sh: $OUT is not a directory" >&2
    exit 0
  fi
fi
# Reuse collect's README writer by invoking just the hashing tail via collect after env is already there.
# Safer: run the same Python block independently.
python3 - "$OUT" <<'PY'
import hashlib, pathlib, sys, os
out = pathlib.Path(sys.argv[1])
rows = []
for p in sorted(out.iterdir()):
    if p.name in ("README.md", "SHA256SUMS") or not p.is_file():
        continue
    h = hashlib.sha256(p.read_bytes()).hexdigest()
    rows.append((h, p.stat().st_size, p.name))
(out / "SHA256SUMS").write_text("\n".join(f"{h}  {name}" for h, _, name in rows) + ("\n" if rows else ""))
readme = []
readme.append("# Lake certificate bundle")
readme.append("")
readme.append("This directory is a real Lean lake-build / kernel-certificate attempt")
readme.append("from this repository's own committed lake-manifest.json.")
readme.append("A hand-written CI_RUN summary is not a certificate.")
readme.append("Third-party or dummy checkers do not prove or pass anything;")
readme.append("the final pass, if any, rests only on the Lean kernel and #print axioms.")
readme.append("")
commit_file = out / "commit.txt"
if commit_file.exists():
    readme.append(f"Commit: {commit_file.read_text().strip()}")
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
present = {p.name for p in out.iterdir() if p.is_file()}
missing = [p.name for p in sorted(out.iterdir()) if p.name.startswith("MISSING-")]
if "lake-build.log" not in present:
    readme.append("Note: lake-build.log is missing from this bundle.")
    readme.append("")
axiomish = sorted(n for n in present if any(k in n.lower() for k in ("axiom", "print-axiom", "print_axiom")))
if not axiomish:
    readme.append("Note: #print axioms output is not in this bundle, or the axiom step did not run.")
    readme.append("")
else:
    readme.append("Axiom / #print axioms files: " + ", ".join(axiomish))
    readme.append("")
if missing:
    readme.append("Missing inputs recorded in: " + ", ".join(missing))
    readme.append("")
(out / "README.md").write_text("\n".join(readme) + "\n")
PY
