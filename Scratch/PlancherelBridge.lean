/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import Scratch.MildMomentum

/-!
 # Plancherel bridge for `Ĥ^m` representatives

For `G ∈ Ĥ^m` with `m ≥ 2` (so the representative is in `L¹ ∩ L²`), the
pointwise inverse Fourier transform `𝓕⁻ G` (the function packaged by
`fourierInvBCF`) is an `L²` representative of the `L²` inverse Fourier
transform of `G`.  Consequently it lies in `L²`, its `L²` norm equals the
unweighted `L²` norm of `G` (Plancherel), and its `L²` Fourier transform is
`G` again.  The proof identifies both as tempered distributions and uses
`ae_eq_of_integral_contDiff_smul_eq`.
-/

open MeasureTheory Real Filter Topology Set FourierTransform
open scoped ENNReal ContDiff SchwartzMap

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
namespace PlancherelBridge

open LerayHeat SobolevFourier SobolevHilbert InverseSobolev LerayPressure FourierInvBCF

/-- Self-adjointness of the inverse Fourier transform against a Schwartz
function, for an integrable (not necessarily continuous) `G`. -/
theorem integral_smul_fourierInv_eq {G : E3 → V} (hG : Integrable G) (ψ : 𝓢(E3, ℂ)) :
    ∫ x, ψ x • 𝓕⁻ G x = ∫ ξ, 𝓕⁻ (ψ : E3 → ℂ) ξ • G ξ := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := Real.fourierChar)
    (μ := (volume : Measure E3)) (ν := (volume : Measure E3)) (L := -innerₗ E3)
    (f := (ψ : E3 → ℂ)) (g := G) Real.continuous_fourierChar
    (by
      change Continuous fun p : E3 × E3 => -inner ℝ p.1 p.2
      exact (continuous_fst.inner continuous_snd).neg) (ψ.integrable) hG
  change ∫ ξ, 𝓕⁻ (ψ : E3 → ℂ) ξ • G ξ = _ at h
  rw [h]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  congr 1
  rw [fourierInv_eq]
  simp only [VectorFourier.fourierIntegral, LinearMap.flip_apply, LinearMap.neg_apply,
    innerₗ_apply_apply, neg_neg, real_inner_comm]

/-- `G ∈ Ĥ^m` as an element of `L²`. -/
def toL2V {m : ℕ} (G : Hm m) : L2V := (memLp_coe_Hm G).toLp _

lemma coeFn_toL2V {m : ℕ} (G : Hm m) : (toL2V G : E3 → V) =ᵐ[volume] (G : E3 → V) :=
  (memLp_coe_Hm G).coeFn_toLp

/-- **Plancherel bridge.** For `G ∈ Ĥ^m`, `m ≥ 2`, the `L²` inverse Fourier
transform of `G` is represented by the pointwise `fourierInvBCF G`. -/
theorem coeFn_fourierInv_toL2V {m : ℕ} (hm : 2 ≤ m) (G : Hm m) :
    ((𝓕⁻ (toL2V G) : L2V) : E3 → V) =ᵐ[volume] fourierInvBCF hm G := by
  have hGi := integrable_of_Hm hm G
  refine ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp _).locallyIntegrable (by norm_num))
    (fourierInvBCF hm G).continuous.locallyIntegrable ?_
  intro φ hφ hφc
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hφc.comp_left rfl
  have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ) := by fun_prop
  set ψ : 𝓢(E3, ℂ) := hg₁.toSchwartzMap hg₂
  have eψ : ∀ x, ψ x = (φ x : ℂ) := fun x => rfl
  have r : ∀ (f : E3 → V), (∫ x, φ x • f x) = ∫ x, ψ x • f x := fun f =>
    integral_congr_ae (Eventually.of_forall fun x => by
      simp only; rw [eψ]; exact (Complex.coe_smul _ _).symm)
  refine (r _).trans (Eq.trans ?_ (r _).symm)
  have h1 : ∫ x, ψ x • ((𝓕⁻ (toL2V G) : L2V) : E3 → V) x =
      ((𝓕⁻ (toL2V G) : L2V) : 𝓢'(E3, V)) ψ :=
    (Lp.toTemperedDistribution_apply _ ψ).symm
  rw [h1, ← Lp.fourierInv_toTemperedDistribution_eq, TemperedDistribution.fourierInv_apply,
    Lp.toTemperedDistribution_apply, SchwartzMap.fourierInv_coe]
  rw [integral_congr_ae (by filter_upwards [coeFn_toL2V G] with ξ hξ; rw [hξ]),
    ← integral_smul_fourierInv_eq hGi ψ]
  rfl

/-- The pointwise inverse transform of `G ∈ Ĥ^m` (`m ≥ 2`) is in `L²`. -/
theorem memLp_fourierInvBCF {m : ℕ} (hm : 2 ≤ m) (G : Hm m) :
    MemLp (fourierInvBCF hm G : E3 → V) 2 volume :=
  (Lp.memLp _).ae_eq (coeFn_fourierInv_toL2V hm G)

/-- **Plancherel for `Ĥ^m` representatives.** -/
theorem lintegral_fourierInvBCF_sq {m : ℕ} (hm : 2 ≤ m) (G : Hm m) :
    ∫⁻ x, ‖fourierInvBCF hm G x‖ₑ ^ 2 = ∫⁻ ξ, ‖(G : E3 → V) ξ‖ₑ ^ 2 := by
  have hn : ‖(𝓕⁻ (toL2V G) : L2V)‖ = ‖toL2V G‖ := by
    rw [← Lp.norm_fourier_eq, fourier_fourierInv_eq]
  have he : eLpNorm ((𝓕⁻ (toL2V G) : L2V) : E3 → V) 2 volume =
      eLpNorm (toL2V G : E3 → V) 2 volume := by
    rw [Lp.norm_def, Lp.norm_def] at hn
    exact (ENNReal.toReal_eq_toReal_iff' (Lp.eLpNorm_ne_top _) (Lp.eLpNorm_ne_top _)).1 hn
  calc ∫⁻ x, ‖fourierInvBCF hm G x‖ₑ ^ 2
      = ∫⁻ x, ‖((𝓕⁻ (toL2V G) : L2V) : E3 → V) x‖ₑ ^ 2 :=
        lintegral_congr_ae ((coeFn_fourierInv_toL2V hm G).mono fun x hx => by simp only [hx])
    _ = ∫⁻ x, ‖(toL2V G : E3 → V) x‖ₑ ^ 2 := by rw [lintegral_sq_eq, lintegral_sq_eq, he]
    _ = ∫⁻ ξ, ‖(G : E3 → V) ξ‖ₑ ^ 2 :=
        lintegral_congr_ae ((coeFn_toL2V G).mono fun x hx => by simp only [hx])

/-- The `L²` Fourier transform of the physical (pointwise) inverse transform
of `G ∈ Ĥ^m` (`m ≥ 2`) is `G` again. -/
theorem fourier_toLp_fourierInvBCF {m : ℕ} (hm : 2 ≤ m) (G : Hm m) :
    (𝓕 ((memLp_fourierInvBCF hm G).toLp _ : L2V) : L2V) = toL2V G := by
  have h : ((memLp_fourierInvBCF hm G).toLp _ : L2V) = (𝓕⁻ (toL2V G) : L2V) :=
    Lp.ext ((memLp_fourierInvBCF hm G).coeFn_toLp.trans (coeFn_fourierInv_toL2V hm G).symm)
  rw [h, fourier_fourierInv_eq]

#print axioms PlancherelBridge.integral_smul_fourierInv_eq
#print axioms PlancherelBridge.coeFn_fourierInv_toL2V
#print axioms PlancherelBridge.memLp_fourierInvBCF
#print axioms PlancherelBridge.lintegral_fourierInvBCF_sq
#print axioms PlancherelBridge.fourier_toLp_fourierInvBCF

end PlancherelBridge
