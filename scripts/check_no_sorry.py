#!/usr/bin/env python3
"""Fail if any tracked .lean file contains sorry/admit/native_decide or an axiom declaration (comments and strings ignored)."""
import re, subprocess, sys
def strip(s):
    out=[];i=0;d=0
    while i<len(s):
        if s.startswith('/-',i): d+=1;i+=2;continue
        if d and s.startswith('-/',i): d-=1;i+=2;continue
        if d: i+=1;continue
        if s.startswith('--',i):
            j=s.find('\n',i); i=len(s) if j<0 else j; continue
        if s[i]=='"':
            j=i+1
            while j<len(s) and s[j]!='"': j+= 2 if s[j]=='\\' else 1
            out.append('""');i=j+1;continue
        out.append(s[i]);i+=1
    return ''.join(out)
bad=[]
for f in subprocess.check_output(['git','ls-files','*.lean']).decode().split():
    for n,l in enumerate(strip(open(f).read()).split('\n'),1):
        if re.search(r'\b(sorry|admit|native_decide)\b',l) or re.match(r'\s*(@\[[^\]]*\]\s*)?(private\s+|protected\s+|noncomputable\s+)*axiom\s',l):
            bad.append(f"{f}:{n}: {l.strip()}")
print("\n".join(bad) if bad else "OK: no sorry/admit/native_decide, no axiom declarations")
sys.exit(1 if bad else 0)
