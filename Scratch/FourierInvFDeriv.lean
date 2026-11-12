import Scratch.FourierInvBCF
import Scratch.InclNSN
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Spatial Fréchet derivative of the inverse Fourier transform on `Ĥ^m`

For `m ≥ 3`, the inverse Fourier transform of an `Ĥ^m` representative is
`C¹`, and its spatial Fréchet derivative in direction `v` is the inverse
Fourier transform of the directional multiplier `(2πi) ⟨ξ, v⟩`, packaged
as `∑ j, vⱼ • 𝓕⁻ (dHⱼ G)`.  Statements are written in terms of
`fourierInvBCF` so that `𝓕⁻` does not appear in elaborated types. -/

open MeasureTheory FourierTransform Real Filter Topology Set
open scoped ENNReal InnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

noncomputable section
namespace FourierInvFDeriv

open LerayHeat SobolevHilbert InverseSobolev NonlinearHm InclNSN
  FourierInvBCF SobolevFourier NonlinearSmooth VectorFourier

lemma two_le_of_three {m : ℕ} (hm : 3 ≤ m) : 2 ≤ m :=
  le_trans (by norm_num : 2 ≤ 3) hm

lemma two_le_pred_of_three {m : ℕ} (hm : 3 ≤ m) : 2 ≤ m - 1 := by
  omega

/-- Spatial Fréchet derivative of `x ↦ 𝓕⁻ G x`, as a continuous linear map
`ℝ³ →L ℂ³`, packaged through `fourierInvBCF` of the derivative multipliers. -/
def spatFDeriv {m : ℕ} (hm : 3 ≤ m) (G : Hm m) (x : E3) : E3 →L[ℝ] V :=
  ∑ j : Fin 3, (EuclideanSpace.proj (𝕜 := ℝ) j).smulRight
    (fourierInvBCF (two_le_pred_of_three hm) (dH (one_le_of_three hm) j G) x)

lemma spatFDeriv_apply {m : ℕ} (hm : 3 ≤ m) (G : Hm m) (x v : E3) :
    spatFDeriv hm G x v =
      ∑ j : Fin 3, v j • fourierInvBCF (two_le_pred_of_three hm)
        (dH (one_le_of_three hm) j G) x := by
  unfold spatFDeriv
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ContinuousLinearMap.smulRight_apply]
  rfl

/-- The symbol of the directional derivative agrees a.e. with the corresponding
linear combination of `dH`. -/
lemma coeFn_sum_dH {m : ℕ} (hm : 3 ≤ m) (G : Hm m) (v : E3) :
    ((fun ξ => ∑ j : Fin 3, v j • (dH (one_le_of_three hm) j G : E3 → V) ξ) : E3 → V)
      =ᵐ[volume]
      fun ξ => ((2 * π * Complex.I) * (inner (𝕜 := ℝ) ξ v : ℂ)) • (G : E3 → V) ξ := by
  have h0 := (ac_vol (m - 1)).ae_le (coeFn_dH (one_le_of_three hm) 0 G)
  have h1 := (ac_vol (m - 1)).ae_le (coeFn_dH (one_le_of_three hm) 1 G)
  have h2 := (ac_vol (m - 1)).ae_le (coeFn_dH (one_le_of_three hm) 2 G)
  filter_upwards [h0, h1, h2] with ξ h0ξ h1ξ h2ξ
  have hsum :
      (∑ j : Fin 3, v j • Nonlinear.derivSym j ξ ((G : E3 → V) ξ)) =
        ((2 * π * Complex.I) * (inner (𝕜 := ℝ) ξ v : ℂ)) • (G : E3 → V) ξ := by
    simp only [Nonlinear.derivSym_apply, sym]
    have hinnerℝ : inner (𝕜 := ℝ) ξ v = ∑ j : Fin 3, ξ j * v j := by
      simp only [PiLp.inner_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      -- Real inner product on ℝ is multiplication (via `re (y * conj x)`).
      simp [Inner.inner, mul_comm]
    have hinner : (inner (𝕜 := ℝ) ξ v : ℂ) = ∑ j : Fin 3, (ξ j : ℂ) * (v j : ℂ) := by
      rw [hinnerℝ, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun j _ => Complex.ofReal_mul _ _
    rw [hinner, Finset.mul_sum]
    -- Move the sum out of the scalar on the right, and expand smul_smul on the left.
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_smul_eq_coe_smul_V, smul_smul]
    congr 1
    ring
  -- Expand the left-hand sum using the three coordinate identities.
  have hpts : ∀ j : Fin 3,
      (dH (one_le_of_three hm) j G : E3 → V) ξ =
        Nonlinear.derivSym j ξ ((G : E3 → V) ξ) := by
    intro j
    fin_cases j <;> simp [h0ξ, h1ξ, h2ξ]
  calc
    (∑ j : Fin 3, v j • (dH (one_le_of_three hm) j G : E3 → V) ξ)
        = ∑ j : Fin 3, v j • Nonlinear.derivSym j ξ ((G : E3 → V) ξ) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hpts j]
    _ = ((2 * π * Complex.I) * (inner (𝕜 := ℝ) ξ v : ℂ)) • (G : E3 → V) ξ := hsum

lemma fourierInv_sum_smul (c : Fin 3 → ℝ) (f : Fin 3 → E3 → V)
    (hf : ∀ j, Integrable (f j)) (x : E3) :
    𝓕⁻ (fun ξ => ∑ j : Fin 3, c j • f j ξ) x =
      ∑ j : Fin 3, c j • 𝓕⁻ (f j) x := by
  simp only [fourierInv_eq_fourier_neg, fourier_eq]
  have hterm : ∀ j, Integrable fun ξ : E3 =>
      Real.fourierChar (-inner (𝕜 := ℝ) ξ (-x)) • f j ξ :=
    fun j => (fourierIntegral_convergent_iff (-x)).mpr (hf j)
  have hinter : ∀ j, Integrable fun ξ : E3 =>
      Real.fourierChar (-inner (𝕜 := ℝ) ξ (-x)) • (c j • f j ξ) := by
    intro j
    have hfunj :
        (fun ξ : E3 => Real.fourierChar (-inner (𝕜 := ℝ) ξ (-x)) • (c j • f j ξ)) =
          fun ξ => c j • (Real.fourierChar (-inner (𝕜 := ℝ) ξ (-x)) • f j ξ) := by
      funext ξ
      exact (smul_comm (c j) _ _).symm
    rw [hfunj]
    exact (hterm j).smul (c j)
  have hfun :
      (fun ξ : E3 => Real.fourierChar (-inner (𝕜 := ℝ) ξ (-x)) •
          ∑ j : Fin 3, c j • f j ξ) =
        fun ξ => ∑ j : Fin 3,
          Real.fourierChar (-inner (𝕜 := ℝ) ξ (-x)) • (c j • f j ξ) := by
    funext ξ
    rw [Finset.smul_sum]
  rw [hfun, integral_finset_sum _ (fun j _ => hinter j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hfunj :
      (fun ξ : E3 => Real.fourierChar (-inner (𝕜 := ℝ) ξ (-x)) • (c j • f j ξ)) =
        fun ξ => c j • (Real.fourierChar (-inner (𝕜 := ℝ) ξ (-x)) • f j ξ) := by
    funext ξ
    exact (smul_comm (c j) _ _).symm
  rw [hfunj]
  have hreal :
      (fun ξ : E3 => c j • Real.fourierChar (-inner (𝕜 := ℝ) ξ (-x)) • f j ξ) =
        fun ξ => (c j : ℂ) • (Real.fourierChar (-inner (𝕜 := ℝ) ξ (-x)) • f j ξ) := by
    funext ξ
    exact real_smul_eq_coe_smul_V _ _
  rw [hreal, integral_smul, real_smul_eq_coe_smul_V]

lemma fourier_clm_apply (f : E3 → (E3 →L[ℝ] V)) (hf : Integrable f) (x v : E3) :
    𝓕 f x v = 𝓕 (fun ξ => f ξ v) x := by
  simp only [fourier_eq]
  have hinter : Integrable fun ξ : E3 =>
      Real.fourierChar (-inner (𝕜 := ℝ) ξ x) • f ξ :=
    (fourierIntegral_convergent_iff x).mpr hf
  exact ContinuousLinearMap.integral_apply hinter v

lemma integrable_fourierSMulRight {f : E3 → V}
    (hf : Integrable f) (hf' : Integrable fun v : E3 => ‖v‖ * ‖f v‖) :
    Integrable (fourierSMulRight (innerSL ℝ) f) := by
  have hmeas : AEStronglyMeasurable (fourierSMulRight (innerSL ℝ) f) volume :=
    hf.aestronglyMeasurable.fourierSMulRight
  have hbound :
      Integrable fun v : E3 => (2 * π * ‖(innerSL ℝ : E3 →L[ℝ] E3 →L[ℝ] ℝ)‖) * (‖v‖ * ‖f v‖) :=
    hf'.const_mul _
  refine hbound.mono' hmeas ?_
  filter_upwards with v
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    norm_fourierSMulRight_le (innerSL ℝ) f v

lemma fourierSMulRight_comp_neg_apply (G : E3 → V) (η v : E3) :
    fourierSMulRight (innerSL ℝ) (fun ξ => G (-ξ)) (-η) v =
      ((2 * π * Complex.I) * (inner (𝕜 := ℝ) η v : ℂ)) • G η := by
  rw [fourierSMulRight_apply, neg_neg]
  have hr : innerSL ℝ (-η) v = - inner (𝕜 := ℝ) η v :=
    (innerSL_apply_apply (𝕜 := ℝ) (-η) v).trans (inner_neg_left _ _)
  -- Rewrite under the real-to-complex coercion that `rw` will not traverse.
  refine (congrArg (fun r : ℝ => -(2 * π * Complex.I) • r • G η) hr).trans ?_
  have hneg : ((- inner (𝕜 := ℝ) η v) : ℝ) • G η =
      - (inner (𝕜 := ℝ) η v • G η) := neg_smul _ _
  rw [hneg, smul_neg, neg_smul, neg_neg, real_smul_eq_coe_smul_V, smul_smul]

lemma integrable_comp_neg_of_Hm {m : ℕ} (hm : 2 ≤ m) (G : Hm m) :
    Integrable (fun ξ : E3 => (G : E3 → V) (-ξ)) := by
  have h := integrable_of_Hm hm G
  have hmp : MeasurePreserving (Neg.neg : E3 → E3) volume volume :=
    Measure.measurePreserving_neg volume
  have heq : (fun ξ : E3 => (G : E3 → V) (-ξ)) =
      (G : E3 → V) ∘ (Neg.neg : E3 → E3) := rfl
  rw [heq]
  have hG : Integrable (G : E3 → V) (Measure.map (Neg.neg : E3 → E3) volume) := by
    rwa [hmp.map_eq]
  exact (integrable_map_measure hG.aestronglyMeasurable measurable_neg.aemeasurable).1 hG

/-- Directional evaluation of `spatFDeriv` is the Fourier transform of the
directional multiplier, equivalently `𝓕⁻` of `(2πi) ⟨ξ, v⟩ • G`. -/
lemma spatFDeriv_apply_eq {m : ℕ} (hm : 3 ≤ m) (G : Hm m) (x v : E3) :
    spatFDeriv hm G x v =
      𝓕 (fourierSMulRight (innerSL ℝ) (fun ξ : E3 => (G : E3 → V) (-ξ))) x v := by
  have hf_int : Integrable (fun ξ : E3 => (G : E3 → V) (-ξ)) :=
    integrable_comp_neg_of_Hm (two_le_of_three hm) G
  have hvf_int : Integrable (fun ξ : E3 => ‖ξ‖ * ‖(G : E3 → V) (-ξ)‖) := by
    have h := integrable_moment_comp_neg (n := 1) (by omega : 1 + 2 ≤ m) G
    simpa [pow_one] using h
  have hsmulInt :
      Integrable (fourierSMulRight (innerSL ℝ)
        (fun ξ : E3 => (G : E3 → V) (-ξ))) :=
    integrable_fourierSMulRight hf_int hvf_int
  have hint_dH : ∀ j, Integrable (dH (one_le_of_three hm) j G : E3 → V) :=
    fun j => integrable_of_Hm (two_le_pred_of_three hm)
      (dH (one_le_of_three hm) j G)
  -- 𝓕 (fourierSMulRight ...) x v = 𝓕 (pointwise apply v) x
  have happly :
      𝓕 (fourierSMulRight (innerSL ℝ) (fun ξ : E3 => (G : E3 → V) (-ξ))) x v =
        𝓕 (fun ξ => fourierSMulRight (innerSL ℝ)
          (fun η => (G : E3 → V) (-η)) ξ v) x :=
    fourier_continuousLinearMap_apply (hf := hsmulInt)
  -- 𝓕 h x = 𝓕⁻ (h ∘ neg) x
  have hcomp :
      𝓕 (fun ξ => fourierSMulRight (innerSL ℝ)
          (fun η => (G : E3 → V) (-η)) ξ v) x =
        𝓕⁻ (fun η => fourierSMulRight (innerSL ℝ)
          (fun ξ => (G : E3 → V) (-ξ)) (-η) v) x := by
    let h : E3 → V := fun ξ =>
      fourierSMulRight (innerSL ℝ) (fun η => (G : E3 → V) (-η)) ξ v
    have hEq : 𝓕⁻ (fun η => h (-η)) = 𝓕 h := by
      rw [fourierInv_eq_fourier_comp_neg]
      simp [h, neg_neg]
    exact (congrFun hEq x).symm
  have hsym :
      (fun η : E3 => fourierSMulRight (innerSL ℝ)
          (fun ξ => (G : E3 → V) (-ξ)) (-η) v) =
        fun η => ((2 * π * Complex.I) * (inner (𝕜 := ℝ) η v : ℂ)) •
          (G : E3 → V) η := by
    funext η
    exact fourierSMulRight_comp_neg_apply (G : E3 → V) η v
  have hdH := coeFn_sum_dH hm G v
  rw [spatFDeriv_apply]
  -- fourierInvBCF is definitionally 𝓕⁻ of the representative
  change ∑ j : Fin 3, v j • 𝓕⁻ (dH (one_le_of_three hm) j G : E3 → V) x = _
  rw [← fourierInv_sum_smul v
    (fun j => (dH (one_le_of_three hm) j G : E3 → V)) hint_dH x]
  -- a.e. identification of the symbols
  have hcongr := fourierInv_congr_ae hdH x
  refine hcongr.trans ?_
  rw [← hsym]
  exact hcomp.symm.trans happly.symm

lemma hasFDerivAt_fourierInvBCF {m : ℕ} (hm : 3 ≤ m) (G : Hm m) (x : E3) :
    HasFDerivAt (fun y : E3 => (fourierInvBCF (two_le_of_three hm) G).toFun y)
      (spatFDeriv hm G x) x := by
  have hf_int : Integrable (fun ξ : E3 => (G : E3 → V) (-ξ)) :=
    integrable_comp_neg_of_Hm (two_le_of_three hm) G
  have hvf_int : Integrable (fun ξ : E3 => ‖ξ‖ * ‖(G : E3 → V) (-ξ)‖) := by
    have h := integrable_moment_comp_neg (n := 1) (by omega : 1 + 2 ≤ m) G
    simpa [pow_one] using h
  have hfun :
      (fun y : E3 => (fourierInvBCF (two_le_of_three hm) G).toFun y) =
        𝓕 (fun ξ : E3 => (G : E3 → V) (-ξ)) := by
    funext y
    change 𝓕⁻ (G : E3 → V) y = 𝓕 (fun ξ : E3 => (G : E3 → V) (-ξ)) y
    rw [fourierInv_eq_fourier_comp_neg]
  rw [hfun]
  have hL : spatFDeriv hm G x =
      𝓕 (fourierSMulRight (innerSL ℝ) (fun ξ : E3 => (G : E3 → V) (-ξ))) x := by
    apply ContinuousLinearMap.ext
    intro v
    exact spatFDeriv_apply_eq hm G x v
  rw [hL]
  exact hasFDerivAt_fourier hf_int hvf_int x

#print axioms FourierInvFDeriv.spatFDeriv_apply
#print axioms FourierInvFDeriv.coeFn_sum_dH
#print axioms FourierInvFDeriv.fourierInv_sum_smul
#print axioms FourierInvFDeriv.fourier_clm_apply
#print axioms FourierInvFDeriv.integrable_fourierSMulRight
#print axioms FourierInvFDeriv.fourierSMulRight_comp_neg_apply
#print axioms FourierInvFDeriv.integrable_comp_neg_of_Hm
#print axioms FourierInvFDeriv.spatFDeriv_apply_eq
#print axioms FourierInvFDeriv.hasFDerivAt_fourierInvBCF

end FourierInvFDeriv
