#!/usr/bin/env python3
"""Check the output of `lake env lean scripts/PrintRateAxioms.lean`.

Joins Lean's wrapped continuation lines, then requires one `#print axioms` result for
every theorem named in scripts/PrintRateAxioms.lean, each depending on exactly
[propext, Classical.choice, Quot.sound] (or on no axioms). Prints the normalized
listing and a summary line; exits 1 on any missing name, extra axiom, or error."""
import re, sys
names = re.findall(r'^#print axioms (\S+)', open('scripts/PrintRateAxioms.lean').read(), re.M)
raw = open(sys.argv[1]).read().splitlines()
lines = []
for l in raw:
    if l.startswith(' ') and lines: lines[-1] += ' ' + l.strip()
    elif l.strip(): lines.append(l.strip())
got, bad = {}, []
ok = {'propext', 'Classical.choice', 'Quot.sound'}
for l in lines:
    m = re.match(r"'(.*)' depends on axioms: \[(.*)\]$", l)
    n = re.match(r"'(.*)' does not depend on any axioms$", l)
    if m:
        ax = {a.strip() for a in m.group(2).split(',')}
        got[m.group(1)] = ax
        if not ax <= ok: bad.append(f'NONSTANDARD {m.group(1)}: {sorted(ax - ok)}')
    elif n: got[n.group(1)] = set()
    else: bad.append(f'UNEXPECTED OUTPUT: {l}')
for x in names:
    if x not in got: bad.append(f'MISSING {x}')
for l in lines: print(l)
if bad:
    print('\n'.join(bad)); print(f'RATE AUDIT FAIL ({len(bad)} problems)'); sys.exit(1)
print(f'RATE AUDIT PASS: {len(names)}/{len(names)} theorems depend only on propext, Classical.choice, Quot.sound')
