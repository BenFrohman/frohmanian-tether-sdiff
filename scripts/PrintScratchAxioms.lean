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
import Scratch.HeatDeriv
import Scratch.IBPWholeSpace
import Scratch.DuhamelDeriv
import Scratch.MildTimeDeriv
import Scratch.NonlinearSmooth
import Scratch.InclNSN
import Scratch.MildPathSmooth

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
#print axioms KatoPonceCommutator.integral_gradNormSq_sq
#print axioms KatoPonceCommutator.integral_gradNormSq_sq_le_of_hasCompactSupport
#print axioms KatoPonceCommutator.h3GagliardoNirenberg
#print axioms KatoPonceCommutator.integral_gradNormSq_sq_le_of_energy
#print axioms KatoPonceCommutator.abs_integral_commutator_order_two
#print axioms KatoPonceCommutator.abs_integral_commutator_order_three
#print axioms KatoPonceCommutator.h3CommutatorEstimate
#print axioms HeatDeriv.lapH
#print axioms HeatDeriv.hasDerivWithinAt_gauss
#print axioms HeatDeriv.hasDerivWithinAt_heatH
#print axioms HeatDeriv.hasDerivWithinAt_heatH_visc
#print axioms IBPWholeSpace.integral_partial_mul
#print axioms IBPWholeSpace.integral_partial_inner
#print axioms DuhamelDeriv.duh_cocycle
#print axioms DuhamelDeriv.tendsto_duhνSame_avg
#print axioms DuhamelDeriv.hasDerivWithinAt_duhνSame_Ici
#print axioms DuhamelDeriv.incl_duhν_to_duhνSame
#print axioms DuhamelDeriv.incl_heatH_of_le
#print axioms DuhamelDeriv.incl_duhνSame_of_le
#print axioms MildTimeDeriv.incl_duhHigh_to_duhνSame
#print axioms MildTimeDeriv.mildS_eq_duhνSame
#print axioms MildTimeDeriv.hasDerivWithinAt_mildS_incl
#print axioms MildTimeDeriv.continuous_mildSDeriv
#print axioms MildTimeDeriv.hasDerivAt_mildS_incl
#print axioms MildTimeDeriv.hasDerivWithinAt_mildS_incl_Ico
#print axioms MildTimeDeriv.contDiffOn_one_inclExt
#print axioms MildTimeDeriv.lapH_heatH
#print axioms MildTimeDeriv.mildSDeriv_eq_lap
#print axioms NonlinearSmooth.isBoundedBilinear_mulF
#print axioms NonlinearSmooth.contDiff_mulF
#print axioms NonlinearSmooth.contDiff_mulF_quad
#print axioms NonlinearSmooth.contDiff_divTensor
#print axioms NonlinearSmooth.contDiff_NSN
#print axioms NonlinearSmooth.contDiff_NSNsucc
#print axioms InclNSN.incl_mulF_of_le
#print axioms InclNSN.incl_dH_of_le
#print axioms InclNSN.incl_NSN_of_le
#print axioms InclNSN.coeFn_NSNsucc
#print axioms InclNSN.incl_NSNsucc
#print axioms InclNSN.incl_incl_NSNsucc
#print axioms MildPathSmooth.incl_nsnExt_eq_NSNsucc
#print axioms MildPathSmooth.mildSDeriv_eq_NSNsucc
#print axioms MildPathSmooth.derivWithin_inclExt_eq_NSNsucc
#print axioms MildPathSmooth.contDiff_lapH
#print axioms MildPathSmooth.contDiffOn_inclExt
#print axioms MildPathSmooth.contDiffOn_inclExt_of_le_two

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
    ``KatoPonceCommutator.abs_integral_commutator_order_one,
    ``KatoPonceCommutator.integral_gradNormSq_sq,
    ``KatoPonceCommutator.integral_gradNormSq_sq_le_of_hasCompactSupport,
    ``KatoPonceCommutator.h3GagliardoNirenberg,
    ``KatoPonceCommutator.integral_gradNormSq_sq_le_of_energy,
    ``KatoPonceCommutator.abs_integral_commutator_order_two,
    ``KatoPonceCommutator.abs_integral_commutator_order_three,
    ``KatoPonceCommutator.h3CommutatorEstimate,
    ``HeatDeriv.lapH,
    ``HeatDeriv.hasDerivWithinAt_heatH,
    ``HeatDeriv.hasDerivWithinAt_heatH_visc,
    ``IBPWholeSpace.integral_partial_mul,
    ``IBPWholeSpace.integral_partial_inner,
    ``DuhamelDeriv.duh_cocycle,
    ``DuhamelDeriv.tendsto_duhνSame_avg,
    ``DuhamelDeriv.hasDerivWithinAt_duhνSame_Ici,
    ``DuhamelDeriv.incl_duhν_to_duhνSame,
    ``DuhamelDeriv.incl_heatH_of_le,
    ``DuhamelDeriv.incl_duhνSame_of_le,
    ``MildTimeDeriv.incl_duhHigh_to_duhνSame,
    ``MildTimeDeriv.mildS_eq_duhνSame,
    ``MildTimeDeriv.hasDerivWithinAt_mildS_incl,
    ``MildTimeDeriv.continuous_mildSDeriv,
    ``MildTimeDeriv.hasDerivAt_mildS_incl,
    ``MildTimeDeriv.hasDerivWithinAt_mildS_incl_Ico,
    ``MildTimeDeriv.contDiffOn_one_inclExt,
    ``MildTimeDeriv.lapH_heatH,
    ``MildTimeDeriv.mildSDeriv_eq_lap,
    ``NonlinearSmooth.isBoundedBilinear_mulF,
    ``NonlinearSmooth.contDiff_mulF,
    ``NonlinearSmooth.contDiff_mulF_quad,
    ``NonlinearSmooth.contDiff_divTensor,
    ``NonlinearSmooth.contDiff_NSN,
    ``NonlinearSmooth.contDiff_NSNsucc,
    ``InclNSN.incl_mulF_of_le,
    ``InclNSN.incl_dH_of_le,
    ``InclNSN.incl_NSN_of_le,
    ``InclNSN.coeFn_NSNsucc,
    ``InclNSN.incl_NSNsucc,
    ``InclNSN.incl_incl_NSNsucc,
    ``MildPathSmooth.incl_nsnExt_eq_NSNsucc,
    ``MildPathSmooth.mildSDeriv_eq_NSNsucc,
    ``MildPathSmooth.derivWithin_inclExt_eq_NSNsucc,
    ``MildPathSmooth.contDiff_lapH,
    ``MildPathSmooth.contDiffOn_inclExt,
    ``MildPathSmooth.contDiffOn_inclExt_of_le_two]
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
