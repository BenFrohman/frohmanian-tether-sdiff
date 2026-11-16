import Scratch.MildJointSmooth
import Scratch.FourierInvFDerivCn

/-! # Joint `C^∞` of the realized mild field

For every `n`, persistence at regularity `k = 3n + 3` puts the included mild
path in `C^n([0, T); Ĥ^{n+3})`; joint `C^n` of `(x, G) ↦ 𝓕⁻ G x` for
`m ≥ n + 3` then gives joint `C^n` of the physical field on `ℝ³ × [0, T)`,
including one-sided derivatives at `t = 0`.  Since `n` is arbitrary the
field is `C^∞` on `ℝ³ × [0, T)`. -/

open MeasureTheory Filter Topology Set
open scoped ContDiff

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 200000

noncomputable section
namespace MildJointSmooth

open LerayHeat SobolevHilbert InverseSobolev PersistenceHm
  MildTimeDeriv MildPathSmooth FeffermanMild FourierInvBCF FourierInvFDeriv
  NavierStokes3D RepairedTether

/-- The realized mild field is jointly `C^n` on `ℝ³ × [0, T)` for every `n`,
including the one-sided time derivatives at `t = 0`. -/
theorem contDiffOn_physicalMild_nat {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀)
    (hdec : FeffermanDecay u₀) {ν : ℝ} (hν : 0 < ν) (n : ℕ) :
    ContDiffOn ℝ n (fun q : E3 × ℝ => physicalMild hf hdec hν q.2 q.1)
      (univ ×ˢ Ico 0 (Tfeff hf hdec hν)) := by
  have hk : 2 ≤ 3 * n + 3 := by omega
  have hle : n + 3 ≤ 3 * n + 3 + 1 := by omega
  have hn : n + 3 + 2 * n ≤ 3 * n + 3 := by omega
  have hm : n + 3 ≤ n + 3 := le_rfl
  have hγ : ContDiffOn ℝ n
      (inclExt hle (Tfeff_nonneg hf hdec hν) (persistPath hf hdec hν hk))
      (Ico 0 (Tfeff hf hdec hν)) :=
    contDiffOn_inclExt hk (by omega : 2 ≤ n + 3) hn hν
      (Tfeff_nonneg hf hdec hν) (persistPath_mildS hf hdec hν hk)
  have hC := contDiffOn_uncurry_clm_path hm realifyCLM hγ
  refine hC.congr ?_
  intro q hq
  have hphys := physicalMild_eq_inclExt hf hdec hν hk hle hq.2
  have hreal := physicalOfHm_eq_realify_BCF (two_le_of_add_three hm)
    (inclExt hle (Tfeff_nonneg hf hdec hν) (persistPath hf hdec hν hk) q.2) q.1
  calc
    physicalMild hf hdec hν q.2 q.1
        = physicalOfHm
            (inclExt hle (Tfeff_nonneg hf hdec hν)
              (persistPath hf hdec hν hk) q.2) q.1 :=
          congrArg (fun f => f q.1) hphys
    _ = realifyCLM
          (uncurryFourierInvBCF (two_le_of_add_three hm)
            (q.1, inclExt hle (Tfeff_nonneg hf hdec hν)
              (persistPath hf hdec hν hk) q.2)) := by
          simpa [uncurryFourierInvBCF] using hreal.symm

/-- The realized mild field is jointly `C^∞` on `ℝ³ × [0, T)`, including the
one-sided time derivatives at `t = 0`. -/
theorem contDiffOn_physicalMild {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀)
    (hdec : FeffermanDecay u₀) {ν : ℝ} (hν : 0 < ν) :
    ContDiffOn ℝ ∞ (fun q : E3 × ℝ => physicalMild hf hdec hν q.2 q.1)
      (univ ×ˢ Ico 0 (Tfeff hf hdec hν)) :=
  contDiffOn_infty.2 fun n => contDiffOn_physicalMild_nat hf hdec hν n

#print axioms MildJointSmooth.contDiffOn_physicalMild_nat
#print axioms MildJointSmooth.contDiffOn_physicalMild

end MildJointSmooth
