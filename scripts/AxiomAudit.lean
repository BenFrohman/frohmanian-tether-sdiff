import FrohmanianTether
open Lean Elab Command

/-!
# Strict axiom audit for `FrohmanianTether.*`

For every non-internal declaration (theorems, definitions, structures, instances, ...) defined
in a module under `FrohmanianTether`, compute the axioms it depends on (`collectAxioms`) and
print one line per theorem in the same format as `#print axioms`.

The command raises an **error** (so `lake env lean scripts/AxiomAudit.lean` exits non-zero) if
* any declaration depends on an axiom other than `propext`, `Classical.choice`, `Quot.sound`
  (this includes `sorryAx` and `Lean.ofReduceBool`, i.e. `sorry` and `native_decide`), or
* any `axiom` declaration is made inside the `FrohmanianTether` modules.
-/

elab "#strict_axiom_audit" : command => do
  let env ← getEnv
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut nThm := 0
  let mut nAuto := 0
  let mut nDecl := 0
  let mut lines : Array String := #[]
  let mut bad : Array String := #[]
  for (c, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`FrohmanianTether).isPrefixOf mod do continue
    if c.isInternal then continue
    nDecl := nDecl + 1
    if ci matches .axiomInfo _ then
      bad := bad.push s!"axiom declaration: {c}"
    let axs ← liftCoreM (collectAxioms c)
    let axsSorted := axs
    for a in axsSorted do
      unless std.contains a do bad := bad.push s!"{c} depends on nonstandard axiom {a}"
    if ci matches .thmInfo _ then
      nThm := nThm + 1
      let last := match c with | .str _ s => s | _ => ""
      if last.startsWith "eq_" || ["congr_simp", "inj", "injEq", "sizeOf_spec"].contains last then
        nAuto := nAuto + 1
      let s := if axsSorted.isEmpty then s!"'{c}' does not depend on any axioms"
        else s!"'{c}' depends on axioms: {axsSorted.toList}"
      lines := lines.push s
  for l in lines.qsort (· < ·) do IO.println l
  IO.println s!"AUDIT SUMMARY: theorems audited: {nThm} ({nThm - nAuto} stated in the sources, {nAuto} auto-generated equation/congruence/injectivity lemmas); declarations audited: {nDecl}; violations: {bad.size}"
  if bad.isEmpty then
    IO.println "AUDIT PASS: only propext, Classical.choice, Quot.sound; no sorryAx; no axiom declarations"
  else
    for b in bad do IO.println s!"AUDIT FAIL: {b}"
    throwError m!"strict axiom audit failed with {bad.size} violation(s)"

#strict_axiom_audit
