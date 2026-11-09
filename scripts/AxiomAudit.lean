import FrohmanianTether
open Lean Elab Command
/-- Every theorem in the `FrohmanianTether.*` modules; fail on any nonstandard axiom. -/
elab "#audit_axioms" : command => do
  let env ← getEnv
  let std := [``propext, ``Classical.choice, ``Quot.sound]
  let mut n := 0
  let mut bad := #[]
  for (c, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`FrohmanianTether).isPrefixOf mod do continue
    unless ci matches .thmInfo _ do continue
    if c.isInternal then continue
    n := n + 1
    let axs ← liftCoreM (collectAxioms c)
    for a in axs do
      unless std.contains a do bad := bad.push (c, a)
  logInfo m!"theorems audited: {n}; nonstandard axioms: {bad.size} {bad.toList}"
  if bad.size ≠ 0 then
    throwError "AxiomAudit FAIL: nonstandard axioms present {bad.toList}"
  if n = 0 then
    throwError "AxiomAudit FAIL: audited zero theorems"
#audit_axioms
#print axioms Combined.combined_conditional_capstone
#print axioms ConcreteSDiff.casimir_invariant
