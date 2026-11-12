import Scratch.MildPathSmooth
import Scratch.FeffermanMild
import Scratch.FourierInvBCF
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
  MildTimeDeriv MildPathSmooth FeffermanMild FourierInvBCF
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

#print axioms MildJointSmooth.continuousOn_uncurry_physicalOfHm
#print axioms MildJointSmooth.continuousOn_physicalMild

end MildJointSmooth
