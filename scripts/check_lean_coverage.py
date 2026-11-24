#!/usr/bin/env python3
# Author: Benjamin Stanley Frohman
"""Coverage check: EVERY tracked .lean file (`git ls-files '*.lean'`, only .lake/ left out) must
be, and is reported as, exactly one of:
  (a) BUILT    - a module whose .olean exists after `lake build` and `lake build Scratch`
                 (the module name is the path under a `srcDir` declared in lakefile.lean, or
                 under the repository root);
  (b) CI-RUN   - lakefile.lean, or a scripts/*.lean file that a workflow, a CI shell script or
                 TRUTH_GATE.lock runs by path;
  (c) EXCERPT  - a manuscript statement excerpt whose `-- <file>.lean, line N` provenance names a
                 BUILT file and whose code lines occur verbatim, contiguously, in that file
                 (proof bodies shown as `...`).
Also: scripts/ScratchAxiomAuditAll.lean must import exactly the tracked Scratch/*.lean modules.
Any file in none of the classes FAILS, by name. There is no exclusion list.
Usage: python3 scripts/check_lean_coverage.py [--list-built]"""
import os, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT)

def tracked():
    return [f for f in subprocess.check_output(["git", "ls-files", "*.lean"]).decode().splitlines()
            if f and not f.startswith(".lake/") and "/.lake/" not in f]

def src_dirs():
    lf = open("lakefile.lean", encoding="utf-8").read()
    return sorted({d.strip("/") for d in re.findall(r'srcDir\s*:=\s*"([^"]*)"', lf)} - {"", "."},
                  key=len, reverse=True)

OLEAN_ROOT = ".lake/build/lib/lean"

def module_of(f):
    """(module name, olean path) if f is a built module, else None."""
    rel = f[:-5]
    cands = [rel] + [rel[len(d) + 1:] for d in src_dirs() if rel.startswith(d + "/")]
    for c in cands:
        ol = os.path.join(OLEAN_ROOT, c + ".olean")
        if os.path.isfile(ol):
            return c.replace("/", "."), ol
    return None

def ci_text():
    txt = ""
    wf = ".github/workflows"
    for d, files in [(wf, sorted(os.listdir(wf)) if os.path.isdir(wf) else []),
                     ("scripts", sorted(os.listdir("scripts")))]:
        for n in files:
            if n.endswith((".yml", ".yaml", ".sh")):
                txt += open(os.path.join(d, n), encoding="utf-8").read() + "\n"
    if os.path.isfile("TRUTH_GATE.lock"):
        txt += open("TRUTH_GATE.lock", encoding="utf-8").read()
    return txt

def provenance(path):
    """Source file named by a `-- <file>.lean, line N` header, or by an index.json beside the
    excerpt (key = file name without .lean, field "file")."""
    t = open(path, encoding="utf-8").read()
    m = re.search(r"^-- ([\w./-]+\.lean), lines? (\d+)(?:-\d+)?\s*$", t, re.M)
    if m:
        body = re.sub(r"^\s*/-!.*?-/\s*", "", t[m.end():], count=1, flags=re.S)
        return m.group(1), body
    idx = os.path.join(os.path.dirname(path), "index.json")
    if os.path.isfile(idx):
        import json
        ent = json.load(open(idx, encoding="utf-8")).get(os.path.basename(path)[:-5])
        if isinstance(ent, dict) and "file" in ent:
            return ent["file"], t
    return None, t

def check_excerpt(path, built_files):
    src, body = provenance(path)
    if src is None:
        return "no provenance (no '-- <file>.lean, line N' header and no index.json entry)"
    if src not in built_files:
        return f"provenance file {src} is not a BUILT module"
    lines = [l.strip() for l in body.split("\n") if l.strip()]
    if not lines:
        return "empty excerpt"
    S = [l.strip() for l in open(src, encoding="utf-8").read().split("\n")]
    def same(l, s, last):
        if l == s:
            return True
        if "..." in l and s.startswith(l.split("...")[0].rstrip()):
            return True   # proof body shown as `...`
        return last and s.startswith(l) and s[len(l):].strip() in (":=", ":= by")
    def match_at(i):
        for k, l in enumerate(lines):
            if i + k >= len(S) or not same(l, S[i + k], k == len(lines) - 1):
                return False
        return True
    if any(match_at(i) for i in range(len(S))):
        return None
    return f"code is not a verbatim contiguous block of {src}"

def main():
    files = tracked()
    if not files:
        print("COVERAGE FAIL: git ls-files '*.lean' returned nothing"); return 1
    built, runs, excerpts, fails = {}, [], [], []
    for f in files:
        mo = module_of(f)
        if mo:
            built[f] = mo[0]
    ci = ci_text()
    for f in files:
        if f in built:
            continue
        if f == "lakefile.lean" or (f.startswith("scripts/") and f in ci):
            runs.append(f); continue
        r = check_excerpt(f, built)
        if r is None:
            excerpts.append(f); continue
        fails.append(f"{f}: not built (no {OLEAN_ROOT}/<module>.olean), not run by CI, not a verified excerpt ({r})")
    # the full Scratch audit must import every Scratch module
    audit = "scripts/ScratchAxiomAuditAll.lean"
    scratch = sorted(f[:-5].replace("/", ".") for f in files if f.startswith("Scratch/"))
    if os.path.isfile(audit):
        imps = sorted(re.findall(r"^import\s+(Scratch\.\S+)", open(audit, encoding="utf-8").read(), re.M))
        if imps != scratch:
            fails.append(f"{audit} imports {len(imps)} Scratch modules but {len(scratch)} are tracked; "
                         f"missing {sorted(set(scratch) - set(imps))}, extra {sorted(set(imps) - set(scratch))}")
    elif scratch:
        fails.append(f"{audit} missing")
    if "--list-built" in sys.argv:
        for f in sorted(built):
            print(built[f])
        return 1 if fails else 0
    print(f"COVERAGE: {len(files)} tracked .lean files: {len(built)} BUILT, {len(runs)} CI-RUN, "
          f"{len(excerpts)} EXCERPT, {len(fails)} uncovered")
    for f in runs:
        print(f"  CI-RUN  {f}")
    for f in fails:
        print(f"COVERAGE FAIL: {f}")
    if fails:
        return 1
    print("COVERAGE PASS: every tracked .lean file is built, run by CI, or a verified excerpt of a built file")
    return 0

if __name__ == "__main__":
    sys.exit(main())
