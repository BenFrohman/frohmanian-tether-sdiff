import Scratch.LogBoundLocal
import Scratch.MildExistence
import Scratch.ProductHm
import Scratch.NonlinearHm
import Scratch.InverseSobolev
import Scratch.FeffermanSchwartz
import Scratch.PersistenceHm
import Scratch.KatoPonce
import Scratch.FeffermanMild
import Scratch.KatoPonceCommutator

open Lean Elab Command

/-!
# `#print axioms` and a strict axiom check for the headline Scratch theorems.

Run by the Lean certificate workflow after `lake build Scratch`. The main-library
audit in `scripts/AxiomAudit.lean` / `scripts/PrintAxioms.lean` is left unchanged.
-/

#print axioms LogBoundLocal.bkmLogInequality
#print axioms LogBoundLocal.clay_A_fefferman_of_rate_of_kato
#print axioms MildExistence.local_mild_existence
#print axioms ProductHm.norm_mulF_le
#print axioms ProductHm.eLpNorm_conv_sq_le
#print axioms ProductHm.weighted_conv_tame
#print axioms ProductHm.weighted_conv_le_pow
#print axioms NonlinearHm.norm_NSN_le
#print axioms NonlinearHm.norm_NSN_sub_le
#print axioms InverseSobolev.contDiff_fourierInv_of_all_energy
#print axioms FeffermanSchwartz.fourierInv_fourier_cplx_of_fefferman
#print axioms PersistenceHm.persist_on_minTime
#print axioms PersistenceHm.apriori_double
#print axioms PersistenceHm.persist_chunk_bound
#print axioms PersistenceHm.persist_on_H3_time
#print axioms KatoPonce.katoPonce_h3_energy
#print axioms FeffermanMild.physicalOfHm_toHmFeff
#print axioms FeffermanMild.persist_fefferman
#print axioms FeffermanMild.contDiff_physicalOfHm
#print axioms FeffermanMild.physicalOfHm_incl
#print axioms FeffermanMild.inclMap_persistPath_unique
#print axioms FeffermanMild.physicalMild_zero
#print axioms FeffermanMild.contDiff_physicalMild
#print axioms KatoPonceCommutator.convectiveCommutator_order_one
#print axioms KatoPonceCommutator.abs_integral_commutator_order_one

elab "#strict_scratch_axiom_audit" : command => do
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  -- Fail the job if any of these headline theorems depends on an axiom outside the standard three
  -- (this includes `sorryAx` and `Lean.ofReduceBool`).
  let targets : List Name := [
    ``LogBoundLocal.bkmLogInequality,
    ``LogBoundLocal.clay_A_fefferman_of_rate_of_kato,
    ``MildExistence.local_mild_existence,
    ``ProductHm.norm_mulF_le,
    ``NonlinearHm.norm_NSN_le,
    ``InverseSobolev.contDiff_fourierInv_of_all_energy,
    ``FeffermanSchwartz.fourierInv_fourier_cplx_of_fefferman,
    ``PersistenceHm.persist_on_minTime,
    ``PersistenceHm.persist_chunk_bound,
    ``PersistenceHm.persist_on_H3_time,
    ``KatoPonce.katoPonce_h3_energy,
    ``FeffermanMild.physicalOfHm_toHmFeff,
    ``FeffermanMild.persist_fefferman,
    ``FeffermanMild.physicalMild_zero,
    ``FeffermanMild.contDiff_physicalMild,
    ``KatoPonceCommutator.convectiveCommutator_order_one,
    ``KatoPonceCommutator.abs_integral_commutator_order_one]
  let mut bad : Array String := #[]
  let mut nOk := 0
  for c in targets do
    unless (← getEnv).contains c do
      bad := bad.push s!"missing declaration: {c}"
      continue
    let axs ← liftCoreM (collectAxioms c)
    let mut ok := true
    for a in axs do
      unless std.contains a do
        ok := false
        bad := bad.push s!"{c} depends on nonstandard axiom {a}"
    if ok then nOk := nOk + 1
  IO.println s!"SCRATCH AUDIT SUMMARY: theorems audited: {targets.length}; clean: {nOk}; violations: {bad.size}"
  if bad.isEmpty then
    IO.println "SCRATCH AUDIT PASS: only propext, Classical.choice, Quot.sound; no sorryAx"
  else
    for b in bad do IO.println s!"SCRATCH AUDIT FAIL: {b}"
    throwError m!"scratch axiom audit failed with {bad.size} violation(s)"

#strict_scratch_axiom_audit
