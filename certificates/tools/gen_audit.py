#!/usr/bin/env python3
"""Kernel-certificate helper: list this repository's built Lean modules and write Lean files
that run `collectAxioms` (the function behind `#print axioms`) on every theorem declared in
them.  Usage: python3 certificates/tools/gen_audit.py OUT.lean MODULES.txt

Module names come from scripts/check_lean_coverage.py (lakefile srcDirs; no tracked file is
passed over). MODULES.txt lists every built module, Scratch included (external kernel re-check).
One collectAxioms file is written per top-level module prefix other than Scratch, as
OUT_<prefix>.lean, and their paths are listed in OUT.files; the Scratch library is audited
declaration by declaration by scripts/ScratchAxiomAuditAll.lean."""
import os, sys
out, modlist = sys.argv[1], sys.argv[2]
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'scripts'))
import check_lean_coverage as cov

TEMPLATE = """import Lean
{imports}

open Lean Elab Command

/-- Prints `#print axioms`-style lines for every theorem declared in the listed modules. -/
elab "#kernel_certificate_audit" : command => do
  let env ← getEnv
  let mods : Array Name := #[{names}]
  for m in mods do
    match env.getModuleIdx? m with
    | none => IO.println s!"MODULE NOT LOADED {{m}}"
    | some i =>
      for n in (env.header.moduleData[i.toNat]!).constNames do
        match env.find? n with
        | some (.thmInfo _) =>
          if !n.isInternal then
            let ax ← collectAxioms n
            let axs := ", ".intercalate (ax.toList.map toString)
            if ax.isEmpty then IO.println s!"'{{n}}' does not depend on any axioms [module {{m}}]"
            else IO.println s!"'{{n}}' depends on axioms: [{{axs}}] [module {{m}}]"
        | _ => pure ()

#kernel_certificate_audit
"""

def q(m):
    return '.'.join('«' + p + '»' for p in m.split('.'))

files = cov.tracked()
allmods = sorted(m for m, _ in (x for x in (cov.module_of(f) for f in files) if x))
open(modlist, 'w').write('\n'.join(allmods) + '\n')
groups = {}
for m in allmods:
    if not m.startswith('Scratch.'):
        groups.setdefault(m.split('.')[0], []).append(m)
outs = []
for g, mods in sorted(groups.items()):
    gout = out[:-5] + '_' + g + '.lean'
    outs.append(gout)
    open(gout, 'w').write(TEMPLATE.format(imports='\n'.join('import ' + q(m) for m in mods),
                                          names=', '.join('`' + q(m) for m in mods)))
open(out[:-5] + '.files', 'w').write('\n'.join(outs) + '\n')
nscr = sum(1 for m in allmods if m.startswith('Scratch.'))
print(f'{len(allmods)} built modules: ' + ', '.join(f'{g}: {len(v)}' for g, v in sorted(groups.items()))
      + f'; Scratch: {nscr} (audited by scripts/ScratchAxiomAuditAll.lean)')
