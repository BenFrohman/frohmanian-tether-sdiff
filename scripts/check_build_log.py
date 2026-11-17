#!/usr/bin/env python3
# Author: Benjamin Stanley Frohman
"""Read every line of the given Lean/Lake log(s) and fail on any `sorry` warning, any use of
`sorryAx`, any `Lean.ofReduceBool` (native_decide) or any `error:` line. No file, module or
directory is exempt; every hit is printed with its line number."""
import re, sys

PAT = re.compile(r"declaration uses .sorry.|\bsorryAx\b|\bofReduceBool\b|\berror:")
bad, n = [], 0
for path in sys.argv[1:]:
    with open(path, encoding="utf-8", errors="replace") as f:
        for i, line in enumerate(f, 1):
            n += 1
            if PAT.search(line):
                bad.append(f"{path}:{i}: {line.rstrip()}")
if not sys.argv[1:]:
    print("check_build_log: no log given"); sys.exit(2)
if bad:
    print("TRUTH GATE FAIL: sorry / sorryAx / ofReduceBool / error in the log:\n" + "\n".join(bad))
    sys.exit(1)
print(f"check_build_log: read all {n} lines of {', '.join(sys.argv[1:])}: no sorry, sorryAx, ofReduceBool or error")
