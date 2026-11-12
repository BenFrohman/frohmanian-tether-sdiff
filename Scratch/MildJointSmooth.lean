import Scratch.MildPathSmooth
import Scratch.FeffermanMild
import Scratch.FourierInvBCF
import Scratch.FourierInvFDeriv
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! # Joint space-time smoothness of the realized mild path

The included mild path is `C^n` as an `Ĥ^m`-valued curve when
`m + 2n ≤ k`.  Inverse Fourier transform is a bounded linear map
`Ĥ^m → (ℝ³ →ᵇ ℂ³)` for `m ≥ 2`, which gives joint continuity of the
physical field on `ℝ³ × [0, T)`.  Finite-dimensional `C^{n+1}`
characterization then bootstraps to joint `C^∞`, including the
one-sided time derivative at `t = 0`. -/

open MeasureTheory FourierTransform Real Filter Topology Set
open scoped ENNReal ContDiff

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

noncomputable section
namespace MildJointSmooth

open LerayHeat SobolevHilbert InverseSobolev PersistenceHm
  MildTimeDeriv MildPathSmooth FeffermanMild FourierInvBCF FourierInvFDeriv
  NavierStokes3D RepairedTether

lemma physicalOfHm_eq_realify_BCF {m : ℕ} (hm : 2 ≤ m) (G : Hm m) (x : E3) :
    physicalOfHm G x = realifyCLM (fourierInvBCF hm G x) :=
  rfl

/-- If `γ` is continuous on `[0, T)`, the uncurried physical field is jointly
continuous on `ℝ³ × [0, T)`. -/
theorem continuousOn_uncurry_physicalOfHm {m : ℕ} (hm : 2 ≤ m)
    {T : ℝ} {γ : ℝ → Hm m} (hγ : ContinuousOn γ (Ico 0 T)) :
    ContinuousOn (fun q : E3 × ℝ => physicalOfHm (γ q.2) q.1) (univ ×ˢ Ico 0 T) := by
  have h := continuousOn_uncurry_clm_fourierInvBCF hm realifyCLM hγ
  exact h.congr fun q _ => (physicalOfHm_eq_realify_BCF hm (γ q.2) q.1).symm

lemma physicalMild_eq_inclExt {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀)
    (hdec : FeffermanDecay u₀) {ν : ℝ} (hν : 0 < ν)
    {k m : ℕ} (hk : 2 ≤ k) (hle : m ≤ k + 1)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) (Tfeff hf hdec hν)) :
    physicalMild hf hdec hν t =
      physicalOfHm (inclExt hle (Tfeff_nonneg hf hdec hν)
        (persistPath hf hdec hν hk) t) := by
  have htIcc : t ∈ Icc (0 : ℝ) (Tfeff hf hdec hν) := ⟨ht.1, le_of_lt ht.2⟩
  rw [physicalMild_eq_path hf hdec hν hk htIcc, inclExt_of_mem hle _ _ htIcc,
    physicalOfHm_incl]

/-- The realized mild field is jointly continuous on `ℝ³ × [0, T)`. -/
theorem continuousOn_physicalMild {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀)
    (hdec : FeffermanDecay u₀) {ν : ℝ} (hν : 0 < ν) :
    ContinuousOn (fun q : E3 × ℝ => physicalMild hf hdec hν q.2 q.1)
      (univ ×ˢ Ico 0 (Tfeff hf hdec hν)) := by
  have hk : 2 ≤ 2 := le_rfl
  have hle : (2 : ℕ) ≤ 2 + 1 := by norm_num
  have hγ : ContinuousOn
      (inclExt hle (Tfeff_nonneg hf hdec hν) (persistPath hf hdec hν hk))
      (Ico 0 (Tfeff hf hdec hν)) :=
    (continuous_inclExt hle (Tfeff_nonneg hf hdec hν)
      (persistPath hf hdec hν hk)).continuousOn
  have hC := continuousOn_uncurry_physicalOfHm (by norm_num : 2 ≤ 2) hγ
  refine hC.congr ?_
  intro q hq
  exact congrArg (fun f => f q.1)
    (physicalMild_eq_inclExt hf hdec hν hk hle hq.2)

/-- The realized mild field is jointly `C¹` on `ℝ³ × [0, T)`, including the
one-sided time derivative at `t = 0`. -/
theorem contDiffOn_physicalMild_one {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀)
    (hdec : FeffermanDecay u₀) {ν : ℝ} (hν : 0 < ν) :
    ContDiffOn ℝ 1 (fun q : E3 × ℝ => physicalMild hf hdec hν q.2 q.1)
      (univ ×ˢ Ico 0 (Tfeff hf hdec hν)) := by
  have hk : (2 : ℕ) ≤ 6 := by norm_num
  have hle : (4 : ℕ) ≤ 6 + 1 := by norm_num
  have hn : (4 : ℕ) + 2 * 1 ≤ 6 := by norm_num
  have hγ : ContDiffOn ℝ 1
      (inclExt hle (Tfeff_nonneg hf hdec hν) (persistPath hf hdec hν hk))
      (Ico 0 (Tfeff hf hdec hν)) :=
    contDiffOn_inclExt hk (by norm_num : 2 ≤ 4) hn hν
      (Tfeff_nonneg hf hdec hν) (persistPath_mildS hf hdec hν hk)
  have hC :=
    contDiffOn_uncurry_clm_fourierInvBCF_one (by norm_num : 4 ≤ 4) realifyCLM hγ
  refine hC.congr ?_
  intro q hq
  have hphys := physicalMild_eq_inclExt hf hdec hν hk hle hq.2
  have hreal := physicalOfHm_eq_realify_BCF (by norm_num : 2 ≤ 4)
    (inclExt hle (Tfeff_nonneg hf hdec hν) (persistPath hf hdec hν hk) q.2) q.1
  -- `hphys` identifies the path value; `hreal` unpacks it as `realifyCLM` of
  -- `fourierInvBCF`, which is the uncurried map.
  calc
    physicalMild hf hdec hν q.2 q.1
        = physicalOfHm
            (inclExt hle (Tfeff_nonneg hf hdec hν)
              (persistPath hf hdec hν hk) q.2) q.1 :=
          congrArg (fun f => f q.1) hphys
    _ = realifyCLM
          (uncurryFourierInvBCF (two_le_of_three (four_le (by norm_num : 4 ≤ 4)))
            (q.1, inclExt hle (Tfeff_nonneg hf hdec hν)
              (persistPath hf hdec hν hk) q.2)) := by
          simpa [uncurryFourierInvBCF] using hreal.symm

/-- The realized mild field is jointly `C²` on `ℝ³ × [0, T)`, including the
one-sided time derivative at `t = 0`. -/
theorem contDiffOn_physicalMild_two {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀)
    (hdec : FeffermanDecay u₀) {ν : ℝ} (hν : 0 < ν) :
    ContDiffOn ℝ 2 (fun q : E3 × ℝ => physicalMild hf hdec hν q.2 q.1)
      (univ ×ˢ Ico 0 (Tfeff hf hdec hν)) := by
  have hk : (2 : ℕ) ≤ 9 := by norm_num
  have hle : (5 : ℕ) ≤ 9 + 1 := by norm_num
  have hn : (5 : ℕ) + 2 * 2 ≤ 9 := by norm_num
  have hγ : ContDiffOn ℝ 2
      (inclExt hle (Tfeff_nonneg hf hdec hν) (persistPath hf hdec hν hk))
      (Ico 0 (Tfeff hf hdec hν)) :=
    contDiffOn_inclExt hk (by norm_num : 2 ≤ 5) hn hν
      (Tfeff_nonneg hf hdec hν) (persistPath_mildS hf hdec hν hk)
  have hC :=
    contDiffOn_uncurry_clm_fourierInvBCF_two (by norm_num : 5 ≤ 5) realifyCLM hγ
  refine hC.congr ?_
  intro q hq
  have hphys := physicalMild_eq_inclExt hf hdec hν hk hle hq.2
  have hreal := physicalOfHm_eq_realify_BCF (by norm_num : 2 ≤ 5)
    (inclExt hle (Tfeff_nonneg hf hdec hν) (persistPath hf hdec hν hk) q.2) q.1
  calc
    physicalMild hf hdec hν q.2 q.1
        = physicalOfHm
            (inclExt hle (Tfeff_nonneg hf hdec hν)
              (persistPath hf hdec hν hk) q.2) q.1 :=
          congrArg (fun f => f q.1) hphys
    _ = realifyCLM
          (uncurryFourierInvBCF
            (two_le_of_three (four_le (five_le (by norm_num : 5 ≤ 5))))
            (q.1, inclExt hle (Tfeff_nonneg hf hdec hν)
              (persistPath hf hdec hν hk) q.2)) := by
          simpa [uncurryFourierInvBCF] using hreal.symm

#print axioms MildJointSmooth.continuousOn_uncurry_physicalOfHm
#print axioms MildJointSmooth.continuousOn_physicalMild
#print axioms MildJointSmooth.contDiffOn_physicalMild_one
#print axioms MildJointSmooth.contDiffOn_physicalMild_two

end MildJointSmooth
