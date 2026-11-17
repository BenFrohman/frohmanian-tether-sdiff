#!/usr/bin/env python3
# Author: Benjamin Stanley Frohman
"""Permanent guard. Reads every line of every CI workflow, every .sh, .py and .lean file under
scripts/ and certificates/tools/, lakefile.lean and TRUTH_GATE.lock, and FAILS on any construct that can
make a check pass over a file, a declaration or a failure: inverted grep, exclude options and
lists, carve-outs for drafts, pass-over lists, ignored step errors, failures swallowed by an
always-true alternative, disabled steps, an exit code 0 for a check that did not run, a
hand-written root-directory list, and a non-default lean_lib target that no workflow builds.
Every hit is printed as file:line. There is no allow-list; the patterns below are assembled
from pieces only so that this file does not match itself."""
import os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT)
J = "".join
PATTERNS = [
    (re.compile(J(["\\bgrep\\b[^\\n|]*\\s-[a-zA-Z]*", "v"]) + r"\b|" + J(["--invert", "-match"])), "inverted grep"),
    (re.compile(J(["--", "exclude"])), "exclude option"),
    (re.compile(J(["draft", "[_ -]?", "dir"]), re.I), "carve-out for drafts"),
    (re.compile(J(["\\bex", "clude[ds]?\\b\\s*[:=\\[(]|EX", "CLUDED|\\bex", "clude_|\\bex", "cluded_|[\"']ex", "cluded[\"']"])), "exclusion list"),
    (re.compile(J(["--sk", "ip\\b|\\bSK", "IP_|\\bsk", "ip_(list|files|dirs|modules|paths)|\\bsk", "ipped_"])), "skip list"),
    (re.compile(J(["contin", "ue-on-", "error"])), "ignored step error"),
    (re.compile(J(["\\|\\|\\s*", "(true|:)\\b"])), "failure swallowed"),
    (re.compile(J(["\\bif:\\s*", "(false|\\$\\{\\{\\s*false)"])), "disabled step"),
    (re.compile(J(["lean", "_roots"])), "hand-written root list"),
    (re.compile(J(["NOT ", "RUN"]) + r".*\bexit\s+0\b"), "check that did not run exits 0"),
]

def files():
    out = []
    wf = ".github/workflows"
    if os.path.isdir(wf):
        out += [os.path.join(wf, n) for n in sorted(os.listdir(wf)) if n.endswith((".yml", ".yaml"))]
    for top in ["scripts", "certificates/tools"]:
        if not os.path.isdir(top):
            continue
        for dp, dn, fs in os.walk(top):
            dn[:] = sorted(dn)
            out += [os.path.join(dp, n) for n in sorted(fs) if n.endswith((".sh", ".py", ".lean"))]
    out += [p for p in ["lakefile.lean", "TRUTH_GATE.lock", "Makefile"] if os.path.isfile(p)]
    return out

bad, nlines, fl = [], 0, files()
for p in fl:
    for i, line in enumerate(open(p, encoding="utf-8", errors="replace"), 1):
        nlines += 1
        for rx, what in PATTERNS:
            if rx.search(line):
                bad.append(f"{p}:{i}: {what}: {line.strip()[:160]}")

# every non-default lean_lib must be built by some workflow
if os.path.isfile("lakefile.lean"):
    lf = open("lakefile.lean", encoding="utf-8").read()
    wf_txt = "".join(open(p, encoding="utf-8").read() for p in fl if p.startswith(".github/"))
    sh_txt = "".join(open(p, encoding="utf-8").read() for p in fl if p.endswith(".sh"))
    for m in re.finditer(r"(@\[default_target\]\s*)?lean_lib\s+«?(\w+)»?", lf):
        if not m.group(1):
            name = m.group(2)
            if not re.search(rf"lake build {re.escape(name)}\b", wf_txt + sh_txt):
                bad.append(f"lakefile.lean: non-default target lean_lib {name} is built by no workflow or CI script")

if bad:
    print("NO-SKIP GUARD FAIL:\n" + "\n".join(bad)); sys.exit(1)
print(f"NO-SKIP GUARD PASS: read {nlines} lines in {len(fl)} files; no skip, exclusion or swallowed failure")
