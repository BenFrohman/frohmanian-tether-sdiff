/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import Scratch.DivergenceWholeSpace
import Scratch.Duhamel
import Scratch.DuhamelDeriv
import Scratch.DuhamelUp
import Scratch.FeffermanMild
import Scratch.FeffermanSchwartz
import Scratch.FeffermanSemantics
import Scratch.FeffermanSobolev
import Scratch.FourierCutoff
import Scratch.FourierEmbedding
import Scratch.FourierInvBCF
import Scratch.FourierInvFDeriv
import Scratch.FourierInvFDerivCn
import Scratch.GradBound
import Scratch.HeatDeriv
import Scratch.HeatSobolev
import Scratch.IBPWholeSpace
import Scratch.InclNSN
import Scratch.InverseSobolev
import Scratch.KatoContinuation
import Scratch.KatoMaximal
import Scratch.KatoMaximalProperties
import Scratch.KatoPonce
import Scratch.KatoPonceCommutator
import Scratch.KatoPonceHypotheses
import Scratch.KatoSemantics
import Scratch.LerayHeat
import Scratch.LerayPressure
import Scratch.LogBound
import Scratch.LogBoundLocal
import Scratch.MildDivFree
import Scratch.MildEnergy
import Scratch.MildEnergyIneq
import Scratch.MildExistence
import Scratch.MildFlux
import Scratch.MildJointSmooth
import Scratch.MildJointSmoothInf
import Scratch.MildMomentum
import Scratch.MildPathSmooth
import Scratch.MildPressureSmooth
import Scratch.MildReal
import Scratch.MildTimeDeriv
import Scratch.Nonlinear
import Scratch.NonlinearHm
import Scratch.NonlinearSmooth
import Scratch.PersistenceHm
import Scratch.PlancherelBridge
import Scratch.ProductEstimate
import Scratch.ProductH3
import Scratch.ProductHm
import Scratch.R3BKMContinuation
import Scratch.RepairedTetherRate
import Scratch.SobolevBridge
import Scratch.SobolevEmbedding
import Scratch.SobolevFourier
import Scratch.SobolevHilbert
import Scratch.TetherRateCounterexample
import Scratch.TetherRateStatus

/-!
# scripts.ScratchAxiomAuditAll

Strict axiom audit of EVERY non-internal declaration defined in a `Scratch.*` module.
The import list above is every tracked `Scratch/*.lean` file; `scripts/check_lean_coverage.py`
fails if it differs from `git ls-files 'Scratch/*.lean'`. Raises an error (non-zero exit) if any
declaration depends on an axiom other than `propext`, `Classical.choice`, `Quot.sound`, or if any
`axiom` declaration is made in a `Scratch` module. No declaration is skipped.
-/

open Lean Elab Command

elab "#scratch_full_axiom_audit" : command => do
  let env ← getEnv
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut nThm := 0
  let mut nDecl := 0
  let mut bad : Array String := #[]
  let mut lines : Array String := #[]
  for (c, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`Scratch).isPrefixOf mod do continue
    if c.isInternal then continue
    nDecl := nDecl + 1
    if ci matches .axiomInfo _ then
      bad := bad.push s!"axiom declaration: {c}"
    let axs ← liftCoreM (collectAxioms c)
    for a in axs do
      unless std.contains a do bad := bad.push s!"{c} depends on nonstandard axiom {a}"
    if ci matches .thmInfo _ then
      nThm := nThm + 1
      lines := lines.push (if axs.isEmpty then s!"'{c}' does not depend on any axioms"
        else s!"'{c}' depends on axioms: {axs.toList}")
  for l in lines.qsort (· < ·) do IO.println l
  IO.println s!"SCRATCH FULL AUDIT SUMMARY: modules: {env.header.moduleNames.toList.filter (fun m => (`Scratch).isPrefixOf m) |>.length}; theorems audited: {nThm}; declarations audited: {nDecl}; violations: {bad.size}"
  if bad.isEmpty then
    IO.println "SCRATCH FULL AUDIT PASS: only propext, Classical.choice, Quot.sound; no axiom declarations"
  else
    for b in bad do IO.println s!"SCRATCH FULL AUDIT FAIL: {b}"
    throwError m!"scratch full axiom audit failed with {bad.size} violation(s)"

#scratch_full_axiom_audit
