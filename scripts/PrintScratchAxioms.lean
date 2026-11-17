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
import Scratch.KatoPonceHypotheses
import Scratch.HeatDeriv
import Scratch.IBPWholeSpace
import Scratch.DuhamelDeriv
import Scratch.MildTimeDeriv
import Scratch.NonlinearSmooth
import Scratch.InclNSN
import Scratch.MildPathSmooth
import Scratch.FourierInvBCF
import Scratch.MildJointSmooth
import Scratch.FourierInvFDeriv
import Scratch.LerayPressure
import Scratch.DivergenceWholeSpace
import Scratch.FourierInvFDerivCn
import Scratch.MildJointSmoothInf
import Scratch.MildDivFree
import Scratch.MildReal
import Scratch.MildMomentum
import Scratch.PlancherelBridge
import Scratch.MildEnergy
import Scratch.MildEnergyIneq
import Scratch.MildPressureSmooth
import Scratch.MildFlux
import Scratch.KatoMaximal

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
#print axioms InverseSobolev.integral_norm_coeFn_le
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
#print axioms KatoPonceCommutator.katoPonce_h3_energy'
#print axioms KatoPonceHypotheses.wordDeriv_laplacian_eq
#print axioms KatoPonceHypotheses.wordDeriv_pressureGradient_eq
#print axioms KatoPonceHypotheses.div_wordDeriv_eq
#print axioms KatoPonceHypotheses.h3PartialCommutation_of_contDiff
#print axioms KatoPonceHypotheses.h3PartialCommutation
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
#print axioms FourierInvBCF.isBoundedLinearMap_fourierInvBCF
#print axioms FourierInvBCF.continuous_uncurry_fourierInv
#print axioms FourierInvBCF.continuousOn_uncurry_clm_fourierInvBCF
#print axioms FourierInvBCF.contDiffOn_fourierInvBCF
#print axioms MildJointSmooth.continuousOn_physicalMild
#print axioms FourierInvFDeriv.hasFDerivAt_fourierInvBCF
#print axioms FourierInvFDeriv.fourierInvBCF_eq_integral_spatFDeriv
#print axioms FourierInvFDeriv.hasFDerivAt_uncurryFourierInvBCF
#print axioms LerayPressure.memLp_coe_Hm
#print axioms LerayPressure.memLp_lerayPressureHm
#print axioms LerayPressure.abs_rieszCoeff_le
#print axioms LerayPressure.rieszSym_norm_le
#print axioms LerayPressure.norm_rieszMul_le
#print axioms LerayPressure.norm_lerayPressureHm_le
#print axioms LerayPressure.continuous_lerayPressure
#print axioms LerayPressure.abs_lerayPressure_le
#print axioms LerayPressure.bddAbove_lerayPressure
#print axioms LerayPressure.contDiff_physicalInv
#print axioms LerayPressure.contDiff_lerayPressure
#print axioms LerayPressure.contDiff_two_lerayPressure
#print axioms LerayPressure.contDiff_five_lerayPressure
#print axioms FourierInvFDeriv.continuous_jointFDeriv
#print axioms FourierInvFDeriv.contDiff_one_uncurryFourierInvBCF
#print axioms FourierInvFDeriv.contDiffOn_uncurryFourierInvBCF_path
#print axioms FourierInvFDeriv.contDiffOn_uncurry_clm_fourierInvBCF_one
#print axioms MildJointSmooth.contDiffOn_physicalMild_one
#print axioms FourierInvFDeriv.hasFDerivAt_evMap
#print axioms FourierInvFDeriv.continuous_evFDeriv
#print axioms FourierInvFDeriv.contDiff_one_evMap
#print axioms FourierInvFDeriv.contDiff_two_uncurryFourierInvBCF
#print axioms FourierInvFDeriv.contDiffOn_uncurryFourierInvBCF_path_two
#print axioms MildJointSmooth.contDiffOn_physicalMild_two
#print axioms DivergenceWholeSpace.integral_div_eq_zero_of_hasCompactSupport
#print axioms DivergenceWholeSpace.integral_div_eq_zero
#print axioms FourierInvFDeriv.continuous_evMap
#print axioms FourierInvFDeriv.contDiff_uncurryFourierInvBCF
#print axioms FourierInvFDeriv.contDiff_evMap
#print axioms FourierInvFDeriv.contDiffOn_uncurry_path
#print axioms FourierInvFDeriv.contDiffOn_uncurry_clm_path
#print axioms MildJointSmooth.contDiffOn_physicalMild_nat
#print axioms MildJointSmooth.contDiffOn_physicalMild
#print axioms MildDivFree.lerayH_mildS
#print axioms MildDivFree.inner_fourier_eq_zero
#print axioms MildDivFree.lerayH_toHmFeff
#print axioms MildDivFree.div_physicalOfHm_of_lerayH
#print axioms MildDivFree.div_physicalMild
#print axioms MildReal.refl_wmul
#print axioms MildReal.refl_mulF
#print axioms MildReal.refl_NSN3
#print axioms MildReal.refl_NSN
#print axioms MildReal.refl_toHmFeff
#print axioms MildReal.vconj_fourierInv
#print axioms MildReal.isMild_reflPath
#print axioms MildReal.refl_persistPath
#print axioms MildReal.refl_persistPath_high
#print axioms MildReal.cplx_physicalMild
#print axioms MildMomentum.fourier_conv_eq
#print axioms MildMomentum.fourierInv_mulF
#print axioms MildMomentum.fourierInv_dH_mulF_Lij
#print axioms MildMomentum.sum_fourierInv_dH_self
#print axioms MildMomentum.realify_fourierInv_divTensor
#print axioms MildMomentum.leray_sub_divTensor_coord_ae
#print axioms MildMomentum.realify_fourierInv_leray_sub
#print axioms MildMomentum.realify_fourierInv_NSN
#print axioms MildMomentum.physicalOfHm_NSNsucc
#print axioms MildMomentum.laplacian_physicalOfHm
#print axioms MildMomentum.momentum_physicalMild
#print axioms PlancherelBridge.integral_smul_fourierInv_eq
#print axioms PlancherelBridge.coeFn_fourierInv_toL2V
#print axioms PlancherelBridge.memLp_fourierInvBCF
#print axioms PlancherelBridge.lintegral_fourierInvBCF_sq
#print axioms PlancherelBridge.fourier_toLp_fourierInvBCF
#print axioms MildEnergy.integral_inner_fourierInvBCF
#print axioms MildEnergy.dw_fourierInvBCF
#print axioms MildEnergy.integral_inner_wordDeriv
#print axioms MildEnergy.physical_pairing_eq
#print axioms MildEnergy.sobolevEnergy_physicalOfHm
#print axioms MildEnergy.hsSq_physicalOfHm
#print axioms MildEnergy.timeSliceDeriv_physicalMild
#print axioms MildEnergy.hsSq_physicalMild
#print axioms MildEnergy.h3EnergyRightDerivativeFormula_physicalMild
#print axioms MildEnergyIneq.integral_inner_convective_eq_zero
#print axioms MildEnergyIneq.re_integral_inner_NSN_eq_zero
#print axioms MildEnergyIneq.lintegral_physicalOfHm_sq
#print axioms MildEnergyIneq.re_inner_mildSDeriv_nonpos
#print axioms MildEnergyIneq.energyInequality_physicalMild
#print axioms MildPressureSmooth.contDiff_lerayPressureHm
#print axioms MildPressureSmooth.lerayPressure_congr
#print axioms MildPressureSmooth.presMild_eq_inclExt
#print axioms MildPressureSmooth.contDiffOn_presMild_nat
#print axioms MildPressureSmooth.contDiffOn_presMild
#print axioms MildPressureSmooth.isFeffermanSolutionOn_physicalMild
#print axioms MildFlux.wordIBP_of_tame
#print axioms MildFlux.h3IBPVanishingFlux_of_tame
#print axioms MildFlux.tame_physicalOfHm
#print axioms MildFlux.tame_lerayPressure
#print axioms MildFlux.h3IBPVanishingFlux_physicalMild
#print axioms KatoMaximal.isFeffermanSolutionOn_mono
#print axioms KatoMaximal.isFeffermanSolutionOn_physicalMild_le
#print axioms KatoMaximal.sobolevEnergy_physicalMild_lt_top
#print axioms KatoMaximal.continuous_hsSq_physicalMild
#print axioms KatoMaximal.katoPonce_h3_energy_physicalMild
#print axioms KatoMaximal.restart_from_slice
#print axioms KatoMaximal.unique_inclMap_of_eq_incl
#print axioms KatoMaximal.inclMap_glue_unique
#print axioms KatoMaximal.incl_persistPath_endpoint
#print axioms KatoMaximal.restartTime_eq
#print axioms KatoMaximal.extend_persistPath
#print axioms KatoMaximal.inclMap_restart_unique
#print axioms KatoMaximal.restartPath_mildS
#print axioms KatoMaximal.MildPath.next_t_gap_ge
#print axioms KatoMaximal.iteratePath_t_linear
#print axioms KatoMaximal.mild_blowup_alternative
#print axioms KatoMaximal.iteratePath_t_le
#print axioms KatoMaximal.IccExtend_iteratePath_mono
#print axioms KatoMaximal.physicalMaximal_eq_iterate
#print axioms KatoMaximal.presMaximal_eq_iterate

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
    ``KatoPonceCommutator.katoPonce_h3_energy',
    ``KatoPonceHypotheses.wordDeriv_laplacian_eq,
    ``KatoPonceHypotheses.wordDeriv_pressureGradient_eq,
    ``KatoPonceHypotheses.div_wordDeriv_eq,
    ``KatoPonceHypotheses.h3PartialCommutation_of_contDiff,
    ``KatoPonceHypotheses.h3PartialCommutation,
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
    ``MildPathSmooth.contDiffOn_inclExt_of_le_two,
    ``FourierInvBCF.isBoundedLinearMap_fourierInvBCF,
    ``FourierInvBCF.continuous_uncurry_fourierInv,
    ``FourierInvBCF.continuousOn_uncurry_clm_fourierInvBCF,
    ``FourierInvBCF.contDiffOn_fourierInvBCF,
    ``MildJointSmooth.continuousOn_physicalMild,
    ``FourierInvFDeriv.hasFDerivAt_fourierInvBCF,
    ``FourierInvFDeriv.fourierInvBCF_eq_integral_spatFDeriv,
    ``FourierInvFDeriv.hasFDerivAt_uncurryFourierInvBCF,
    ``LerayPressure.memLp_coe_Hm,
    ``LerayPressure.memLp_lerayPressureHm,
    ``LerayPressure.abs_rieszCoeff_le,
    ``LerayPressure.rieszSym_norm_le,
    ``LerayPressure.norm_rieszMul_le,
    ``LerayPressure.norm_lerayPressureHm_le,
    ``LerayPressure.continuous_lerayPressure,
    ``LerayPressure.abs_lerayPressure_le,
    ``LerayPressure.bddAbove_lerayPressure,
    ``LerayPressure.contDiff_physicalInv,
    ``LerayPressure.contDiff_lerayPressure,
    ``LerayPressure.contDiff_two_lerayPressure,
    ``LerayPressure.contDiff_five_lerayPressure,
    ``FourierInvFDeriv.continuous_jointFDeriv,
    ``FourierInvFDeriv.contDiff_one_uncurryFourierInvBCF,
    ``FourierInvFDeriv.contDiffOn_uncurryFourierInvBCF_path,
    ``FourierInvFDeriv.contDiffOn_uncurry_clm_fourierInvBCF_one,
    ``MildJointSmooth.contDiffOn_physicalMild_one,
    ``FourierInvFDeriv.hasFDerivAt_evMap,
    ``FourierInvFDeriv.continuous_evFDeriv,
    ``FourierInvFDeriv.contDiff_one_evMap,
    ``FourierInvFDeriv.contDiff_two_uncurryFourierInvBCF,
    ``FourierInvFDeriv.contDiffOn_uncurryFourierInvBCF_path_two,
    ``MildJointSmooth.contDiffOn_physicalMild_two,
    ``DivergenceWholeSpace.integral_div_eq_zero_of_hasCompactSupport,
    ``DivergenceWholeSpace.integral_div_eq_zero,
    ``FourierInvFDeriv.continuous_evMap,
    ``FourierInvFDeriv.contDiff_uncurryFourierInvBCF,
    ``FourierInvFDeriv.contDiff_evMap,
    ``FourierInvFDeriv.contDiffOn_uncurry_path,
    ``FourierInvFDeriv.contDiffOn_uncurry_clm_path,
    ``MildJointSmooth.contDiffOn_physicalMild_nat,
    ``MildJointSmooth.contDiffOn_physicalMild,
    ``MildDivFree.lerayH_mildS,
    ``MildDivFree.inner_fourier_eq_zero,
    ``MildDivFree.lerayH_toHmFeff,
    ``MildDivFree.div_physicalOfHm_of_lerayH,
    ``MildDivFree.div_physicalMild,
    ``MildReal.refl_wmul,
    ``MildReal.refl_mulF,
    ``MildReal.refl_NSN3,
    ``MildReal.refl_NSN,
    ``MildReal.refl_toHmFeff,
    ``MildReal.vconj_fourierInv,
    ``MildReal.isMild_reflPath,
    ``MildReal.refl_persistPath,
    ``MildReal.refl_persistPath_high,
    ``MildReal.cplx_physicalMild,
    ``MildMomentum.fourier_conv_eq,
    ``MildMomentum.fourierInv_mulF,
    ``MildMomentum.fourierInv_dH_mulF_Lij,
    ``MildMomentum.sum_fourierInv_dH_self,
    ``MildMomentum.realify_fourierInv_divTensor,
    ``MildMomentum.leray_sub_divTensor_coord_ae,
    ``MildMomentum.realify_fourierInv_leray_sub,
    ``MildMomentum.realify_fourierInv_NSN,
    ``MildMomentum.physicalOfHm_NSNsucc,
    ``MildMomentum.laplacian_physicalOfHm,
    ``MildMomentum.momentum_physicalMild,
    ``PlancherelBridge.integral_smul_fourierInv_eq,
    ``PlancherelBridge.coeFn_fourierInv_toL2V,
    ``PlancherelBridge.memLp_fourierInvBCF,
    ``PlancherelBridge.lintegral_fourierInvBCF_sq,
    ``PlancherelBridge.fourier_toLp_fourierInvBCF,
    ``MildEnergy.integral_inner_fourierInvBCF,
    ``MildEnergy.dw_fourierInvBCF,
    ``MildEnergy.integral_inner_wordDeriv,
    ``MildEnergy.physical_pairing_eq,
    ``MildEnergy.sobolevEnergy_physicalOfHm,
    ``MildEnergy.hsSq_physicalOfHm,
    ``MildEnergy.timeSliceDeriv_physicalMild,
    ``MildEnergy.hsSq_physicalMild,
    ``MildEnergy.h3EnergyRightDerivativeFormula_physicalMild,
    ``MildEnergyIneq.integral_inner_convective_eq_zero,
    ``MildEnergyIneq.re_integral_inner_NSN_eq_zero,
    ``MildEnergyIneq.lintegral_physicalOfHm_sq,
    ``MildEnergyIneq.re_inner_mildSDeriv_nonpos,
    ``MildEnergyIneq.energyInequality_physicalMild,
    ``MildPressureSmooth.contDiff_lerayPressureHm,
    ``MildPressureSmooth.lerayPressure_congr,
    ``MildPressureSmooth.presMild_eq_inclExt,
    ``MildPressureSmooth.contDiffOn_presMild_nat,
    ``MildPressureSmooth.contDiffOn_presMild,
    ``MildPressureSmooth.isFeffermanSolutionOn_physicalMild,
    ``MildFlux.wordIBP_of_tame,
    ``MildFlux.h3IBPVanishingFlux_of_tame,
    ``MildFlux.tame_physicalOfHm,
    ``MildFlux.tame_lerayPressure,
    ``MildFlux.h3IBPVanishingFlux_physicalMild,
    ``KatoMaximal.isFeffermanSolutionOn_mono,
    ``KatoMaximal.isFeffermanSolutionOn_physicalMild_le,
    ``KatoMaximal.sobolevEnergy_physicalMild_lt_top,
    ``KatoMaximal.continuous_hsSq_physicalMild,
    ``KatoMaximal.katoPonce_h3_energy_physicalMild,
    ``KatoMaximal.restart_from_slice,
    ``KatoMaximal.unique_inclMap_of_eq_incl,
    ``KatoMaximal.inclMap_glue_unique,
    ``KatoMaximal.incl_persistPath_endpoint,
    ``KatoMaximal.restartTime_eq,
    ``KatoMaximal.extend_persistPath,
    ``KatoMaximal.inclMap_restart_unique,
    ``KatoMaximal.restartPath_mildS,
    ``KatoMaximal.MildPath.next_t_gap_ge,
    ``KatoMaximal.iteratePath_t_linear,
    ``KatoMaximal.mild_blowup_alternative,
    ``KatoMaximal.iteratePath_t_le,
    ``KatoMaximal.IccExtend_iteratePath_mono,
    ``KatoMaximal.physicalMaximal_eq_iterate,
    ``KatoMaximal.presMaximal_eq_iterate,
    ``KatoMaximal.IccExtend_restartPath_incl,
    ``KatoMaximal.iteratePath_incl_unique,
    ``KatoMaximal.iteratePath_t_unique,
    ``KatoMaximal.IccExtend_iteratePath_incl,
    ``KatoMaximal.physicalMaximal_eq_iterate_high,
    ``KatoMaximal.presMaximal_eq_iterate_high,
    ``KatoMaximal.Smax_unique,
    ``KatoMaximal.Smax_eq_Ici_or_Ico,
    ``KatoMaximal.refl_restartPath,
    ``KatoMaximal.refl_iteratePath,
    ``KatoMaximal.isRealSlice_IccExtend_iteratePath,
    ``KatoMaximal.sobolevEnergy_physicalMaximal_lt_top,
    ``KatoMaximal.hsSq_physicalMaximal,
    ``KatoMaximal.continuousOn_hsSq_physicalMaximal,
    ``KatoMaximal.hsSq_blowup_alternative,
    ``KatoMaximal.physicalMaximal_eq_physicalMild,
    ``KatoMaximal.presMaximal_eq_presMild,
    ``KatoMaximal.isFeffermanSolutionOn_of_empty,
    ``KatoMaximal.isFeffermanSolutionOn_congr,
    ``KatoMaximal.isFeffermanSolutionOn_physicalMaximal_le,
    ``KatoMaximal.lerayH_iteratePath,
    ``KatoMaximal.lerayH_IccExtend_iteratePath,
    ``KatoMaximal.div_physicalMaximal,
    ``KatoMaximal.physicalMaximal_eq_inclExt,
    ``KatoMaximal.contDiffOn_physicalMaximal_of_le,
    ``KatoMaximal.contDiffOn_physicalMaximal_nat,
    ``KatoMaximal.contDiffOn_physicalMaximal]
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
