import Scratch.FourierInvBCF
import Scratch.InclNSN
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! # Spatial Fréchet derivative of the inverse Fourier transform on `Ĥ^m`

For `m ≥ 3`, the inverse Fourier transform of an `Ĥ^m` representative is
`C¹`, and its spatial Fréchet derivative in direction `v` is the inverse
Fourier transform of the directional multiplier `(2πi) ⟨ξ, v⟩`, packaged
as `∑ j, vⱼ • 𝓕⁻ (dHⱼ G)`.  Statements are written in terms of
`fourierInvBCF` so that `𝓕⁻` does not appear in elaborated types. -/

open MeasureTheory FourierTransform Real Filter Topology Set Asymptotics BoundedContinuousFunction
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

/-- Joint evaluation `(x, G) ↦ 𝓕⁻ G x`, packaged through `fourierInvBCF`. -/
def uncurryFourierInvBCF {m : ℕ} (hm : 2 ≤ m) : E3 × Hm m → V :=
  fun p => (fourierInvBCF hm p.2).toFun p.1

lemma continuous_uncurryFourierInvBCF {m : ℕ} (hm : 2 ≤ m) :
    Continuous (uncurryFourierInvBCF hm) := by
  have hCLM : Continuous (fun G : Hm m => fourierInvBCF hm G) :=
    (isBoundedLinearMap_fourierInvBCF hm).toContinuousLinearMap.continuous
  exact continuous_eval.comp ((hCLM.comp continuous_snd).prodMk continuous_fst)

/-- The candidate joint Fréchet derivative of `uncurryFourierInvBCF` at `(x, G)`. -/
def jointFDeriv {m : ℕ} (hm : 3 ≤ m) (x : E3) (G : Hm m) : (E3 × Hm m) →L[ℝ] V :=
  (spatFDeriv hm G x).comp (ContinuousLinearMap.fst ℝ E3 (Hm m)) +
    (evalCLM (𝕜 := ℝ) x).comp
      ((isBoundedLinearMap_fourierInvBCF (two_le_of_three hm)).toContinuousLinearMap.comp
        (ContinuousLinearMap.snd ℝ E3 (Hm m)))

lemma jointFDeriv_apply {m : ℕ} (hm : 3 ≤ m) (x : E3) (G : Hm m) (v : E3) (H : Hm m) :
    jointFDeriv hm x G (v, H) =
      spatFDeriv hm G x v + (fourierInvBCF (two_le_of_three hm) H).toFun x := by
  simp [jointFDeriv, evalCLM]
  rfl

/-- A coordinate of a vector in `ℝ³` is bounded by the Euclidean norm. -/
lemma norm_coord_le (v : E3) (j : Fin 3) : ‖v j‖ ≤ ‖v‖ :=
  PiLp.norm_apply_le v j

lemma norm_spatFDeriv_le {m : ℕ} (hm : 3 ≤ m) (G : Hm m) (x v : E3) :
    ‖spatFDeriv hm G x v‖ ≤
      (∑ j : Fin 3,
        ‖fourierInvBCF (two_le_pred_of_three hm)
          (dH (one_le_of_three hm) j G)‖) * ‖v‖ := by
  rw [spatFDeriv_apply]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ j,
      ‖v j • (fourierInvBCF (two_le_pred_of_three hm)
        (dH (one_le_of_three hm) j G) x)‖ ≤
        ‖fourierInvBCF (two_le_pred_of_three hm)
          (dH (one_le_of_three hm) j G)‖ * ‖v‖ := by
    intro j
    let r : ℝ := v j
    let w : V := fourierInvBCF (two_le_pred_of_three hm)
      (dH (one_le_of_three hm) j G) x
    have hn : ‖r • w‖ = ‖r‖ * ‖w‖ := by
      rw [real_smul_eq_coe_smul_V, norm_smul]
      congr 1
      exact (RCLike.norm_ofReal (K := ℂ) r).trans (Real.norm_eq_abs r).symm
    rw [hn]
    have hmul :=
      mul_le_mul (norm_coord_le v j)
        (BoundedContinuousFunction.norm_coe_le_norm
          (fourierInvBCF (two_le_pred_of_three hm)
            (dH (one_le_of_three hm) j G)) x)
        (norm_nonneg _) (norm_nonneg _)
    simpa [mul_comm] using hmul
  refine (Finset.sum_le_sum fun j _ => hterm j).trans ?_
  rw [← Finset.sum_mul]

/-- The spatial increment of `𝓕⁻ G` is the integral of `spatFDeriv` along the segment. -/
lemma fourierInvBCF_eq_integral_spatFDeriv {m : ℕ} (hm : 3 ≤ m) (G : Hm m) (x v : E3) :
    (fourierInvBCF (two_le_of_three hm) G).toFun (x + v) -
      (fourierInvBCF (two_le_of_three hm) G).toFun x =
      ∫ t in (0:ℝ)..1, spatFDeriv hm G (x + t • v) v := by
  let f : ℝ → V := fun t => (fourierInvBCF (two_le_of_three hm) G).toFun (x + t • v)
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => x + s • v) v t := by
    intro t
    have h := ((hasDerivAt_id t).smul_const v).const_add x
    simpa [id_eq, one_smul] using h
  have hderiv : ∀ t : ℝ, HasDerivAt f (spatFDeriv hm G (x + t • v) v) t := by
    intro t
    exact (hasFDerivAt_fourierInvBCF hm G (x + t • v)).comp_hasDerivAt t (hline t)
  have hcont : Continuous fun t : ℝ => spatFDeriv hm G (x + t • v) v := by
    have hx : Continuous fun t : ℝ => x + t • v :=
      continuous_const.add (continuous_smul.comp
        (continuous_id.prodMk (continuous_const (y := v))))
    have hsp : Continuous fun y : E3 => spatFDeriv hm G y v := by
      simp only [spatFDeriv_apply]
      refine continuous_finset_sum _ fun j _ => ?_
      have hfun :
          (fun y : E3 => v j •
              (fourierInvBCF (two_le_pred_of_three hm)
                (dH (one_le_of_three hm) j G) y)) =
            fun y => (v j : ℂ) •
              (fourierInvBCF (two_le_pred_of_three hm)
                (dH (one_le_of_three hm) j G) y) :=
        funext fun y => real_smul_eq_coe_smul_V _ _
      rw [hfun]
      exact (continuous_const (y := (v j : ℂ))).smul
        (fourierInvBCF (two_le_pred_of_three hm)
          (dH (one_le_of_three hm) j G)).continuous
    exact hsp.comp hx
  have hint : IntervalIntegrable (fun t : ℝ => spatFDeriv hm G (x + t • v) v)
      volume 0 1 :=
    hcont.intervalIntegrable 0 1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hderiv t) hint
  -- ∫ f' = f 1 - f 0
  simpa [f, one_smul, zero_smul] using hFTC.symm

/-- `spatFDeriv` is bilinearly bounded in the representative and the direction. -/
lemma spatFDeriv_le_mul_norm {m : ℕ} (hm : 3 ≤ m) (G : Hm m) (x v : E3) :
    ‖spatFDeriv hm G x v‖ ≤
      (∑ j : Fin 3,
        ‖(isBoundedLinearMap_fourierInvBCF
          (two_le_pred_of_three hm)).toContinuousLinearMap‖ *
          ‖(dH (one_le_of_three hm) j : Hm m →L[ℂ] Hm (m - 1))‖) *
        ‖G‖ * ‖v‖ := by
  refine (norm_spatFDeriv_le hm G x v).trans ?_
  have hsum :
      (∑ j : Fin 3,
        ‖fourierInvBCF (two_le_pred_of_three hm)
          (dH (one_le_of_three hm) j G)‖) ≤
        (∑ j : Fin 3,
          ‖(isBoundedLinearMap_fourierInvBCF
            (two_le_pred_of_three hm)).toContinuousLinearMap‖ *
            ‖(dH (one_le_of_three hm) j : Hm m →L[ℂ] Hm (m - 1))‖) * ‖G‖ := by
    refine (Finset.sum_le_sum fun j _ => ?_).trans_eq (Finset.sum_mul _ _ _).symm
    let L :=
      (isBoundedLinearMap_fourierInvBCF (two_le_pred_of_three hm)).toContinuousLinearMap
    let Dj : Hm m →L[ℂ] Hm (m - 1) := dH (one_le_of_three hm) j
    have hL : ‖L (Dj G)‖ ≤ ‖L‖ * ‖Dj G‖ := L.le_opNorm (Dj G)
    have hd : ‖Dj G‖ ≤ ‖Dj‖ * ‖G‖ := Dj.le_opNorm G
    have hBCF :
        ‖fourierInvBCF (two_le_pred_of_three hm) (Dj G)‖ = ‖L (Dj G)‖ := rfl
    rw [hBCF]
    refine hL.trans ?_
    have hmul := mul_le_mul_of_nonneg_left hd (norm_nonneg L)
    simpa [mul_assoc] using hmul
  exact mul_le_mul_of_nonneg_right hsum (norm_nonneg v)

lemma uncurryFourierInvBCF_add {m : ℕ} (hm : 2 ≤ m) (x : E3) (G H : Hm m) :
    uncurryFourierInvBCF hm (x, G + H) =
      uncurryFourierInvBCF hm (x, G) + uncurryFourierInvBCF hm (x, H) := by
  unfold uncurryFourierInvBCF
  have h := (isBoundedLinearMap_fourierInvBCF hm).map_add G H
  -- h : fourierInvBCF (G+H) = fourierInvBCF G + fourierInvBCF H
  simp [h, BoundedContinuousFunction.add_apply]

lemma uncurryFourierInvBCF_smul {m : ℕ} (hm : 2 ≤ m) (x : E3) (c : ℝ) (G : Hm m) :
    uncurryFourierInvBCF hm (x, c • G) =
      c • uncurryFourierInvBCF hm (x, G) := by
  unfold uncurryFourierInvBCF
  have h := (isBoundedLinearMap_fourierInvBCF hm).map_smul c G
  simp [h, BoundedContinuousFunction.smul_apply]
  rfl

/-- Increment identity for the joint map: the linear terms plus the spatial
remainder of the shifted representative. -/
lemma uncurryFourierInvBCF_remainder {m : ℕ} (hm : 3 ≤ m)
    (x : E3) (G : Hm m) (v : E3) (H : Hm m) :
    uncurryFourierInvBCF (two_le_of_three hm) (x + v, G + H) -
      uncurryFourierInvBCF (two_le_of_three hm) (x, G) -
      jointFDeriv hm x G (v, H) =
      (uncurryFourierInvBCF (two_le_of_three hm) (x + v, G + H) -
        uncurryFourierInvBCF (two_le_of_three hm) (x, G + H) -
        spatFDeriv hm (G + H) x v) + spatFDeriv hm H x v := by
  -- spatFDeriv is linear in G (as a sum of CLMs in G)
  have hlin : spatFDeriv hm (G + H) x v =
      spatFDeriv hm G x v + spatFDeriv hm H x v := by
    simp only [spatFDeriv_apply]
    have hadd := (isBoundedLinearMap_fourierInvBCF
      (two_le_pred_of_three hm)).map_add
    -- dH is additive
    have hdH : ∀ j, dH (one_le_of_three hm) j (G + H) =
        dH (one_le_of_three hm) j G + dH (one_le_of_three hm) j H :=
      fun j => map_add _ _ _
    simp only [hdH, hadd, BoundedContinuousFunction.add_apply]
    refine Eq.trans (Finset.sum_congr rfl fun j _ => smul_add _ _ _) ?_
    exact Finset.sum_add_distrib
  -- Expand the joint derivative and cancel the linear pieces.
  calc
    uncurryFourierInvBCF (two_le_of_three hm) (x + v, G + H) -
        uncurryFourierInvBCF (two_le_of_three hm) (x, G) -
        jointFDeriv hm x G (v, H)
        = uncurryFourierInvBCF (two_le_of_three hm) (x + v, G + H) -
            uncurryFourierInvBCF (two_le_of_three hm) (x, G) -
            (spatFDeriv hm G x v +
              uncurryFourierInvBCF (two_le_of_three hm) (x, H)) := by
          rw [jointFDeriv_apply]; rfl
    _ = (uncurryFourierInvBCF (two_le_of_three hm) (x + v, G + H) -
            uncurryFourierInvBCF (two_le_of_three hm) (x, G + H) -
            spatFDeriv hm (G + H) x v) + spatFDeriv hm H x v := by
          rw [hlin, uncurryFourierInvBCF_add (two_le_of_three hm) x G H]
          abel

lemma norm_spatFDeriv_sub_le {m : ℕ} (hm : 3 ≤ m) (G : Hm m) (y z v : E3) :
    ‖spatFDeriv hm G y v - spatFDeriv hm G z v‖ ≤
      ‖v‖ * ∑ j : Fin 3,
        ‖(fourierInvBCF (two_le_pred_of_three hm)
            (dH (one_le_of_three hm) j G)).toFun y -
          (fourierInvBCF (two_le_pred_of_three hm)
            (dH (one_le_of_three hm) j G)).toFun z‖ := by
  rw [spatFDeriv_apply, spatFDeriv_apply, ← Finset.sum_sub_distrib]
  have hsmul : ∀ j,
      v j • (fourierInvBCF (two_le_pred_of_three hm)
            (dH (one_le_of_three hm) j G) y) -
        v j • (fourierInvBCF (two_le_pred_of_three hm)
            (dH (one_le_of_three hm) j G) z) =
      v j •
        ((fourierInvBCF (two_le_pred_of_three hm)
            (dH (one_le_of_three hm) j G)).toFun y -
          (fourierInvBCF (two_le_pred_of_three hm)
            (dH (one_le_of_three hm) j G)).toFun z) := by
    intro j
    -- Real smul of a difference, rewritten through ℂ to avoid missing ℝ-instances.
    have h1 := real_smul_eq_coe_smul_V (v j)
      (fourierInvBCF (two_le_pred_of_three hm)
        (dH (one_le_of_three hm) j G) y)
    have h2 := real_smul_eq_coe_smul_V (v j)
      (fourierInvBCF (two_le_pred_of_three hm)
        (dH (one_le_of_three hm) j G) z)
    have h3 := real_smul_eq_coe_smul_V (v j)
      ((fourierInvBCF (two_le_pred_of_three hm)
          (dH (one_le_of_three hm) j G)).toFun y -
        (fourierInvBCF (two_le_pred_of_three hm)
          (dH (one_le_of_three hm) j G)).toFun z)
    rw [h1, h2, h3, smul_sub]
    rfl
  simp_rw [hsmul]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ j,
      ‖v j •
          ((fourierInvBCF (two_le_pred_of_three hm)
              (dH (one_le_of_three hm) j G)).toFun y -
            (fourierInvBCF (two_le_pred_of_three hm)
              (dH (one_le_of_three hm) j G)).toFun z)‖ ≤
        ‖v‖ *
          ‖(fourierInvBCF (two_le_pred_of_three hm)
              (dH (one_le_of_three hm) j G)).toFun y -
            (fourierInvBCF (two_le_pred_of_three hm)
              (dH (one_le_of_three hm) j G)).toFun z‖ := by
    intro j
    let r : ℝ := v j
    let w : V :=
      (fourierInvBCF (two_le_pred_of_three hm)
        (dH (one_le_of_three hm) j G)).toFun y -
      (fourierInvBCF (two_le_pred_of_three hm)
        (dH (one_le_of_three hm) j G)).toFun z
    have hn : ‖r • w‖ = ‖r‖ * ‖w‖ := by
      rw [real_smul_eq_coe_smul_V, norm_smul]
      congr 1
      exact (RCLike.norm_ofReal (K := ℂ) r).trans (Real.norm_eq_abs r).symm
    rw [hn]
    exact mul_le_mul_of_nonneg_right (norm_coord_le v j) (norm_nonneg _)
  refine (Finset.sum_le_sum fun j _ => hterm j).trans ?_
  exact (Finset.mul_sum _ _ _).ge

/-- Pointwise spatial remainder along the segment, packaged so the integral
does not parse as a difference of integrals. -/
def spatFDerivDiff {m : ℕ} (hm : 3 ≤ m) (G : Hm m) (x v : E3) (t : ℝ) : V :=
  spatFDeriv hm G (x + t • v) v - spatFDeriv hm G x v

lemma spatial_remainder_eq_integral {m : ℕ} (hm : 3 ≤ m) (G : Hm m) (x v : E3) :
    uncurryFourierInvBCF (two_le_of_three hm) (x + v, G) -
      uncurryFourierInvBCF (two_le_of_three hm) (x, G) -
      spatFDeriv hm G x v =
      ∫ t in (0:ℝ)..1, spatFDerivDiff hm G x v t := by
  have hFTC := fourierInvBCF_eq_integral_spatFDeriv hm G x v
  have hcont : Continuous fun t : ℝ => spatFDeriv hm G (x + t • v) v := by
    have hx : Continuous fun t : ℝ => x + t • v :=
      continuous_const.add (continuous_smul.comp
        (continuous_id.prodMk (continuous_const (y := v))))
    have hsp : Continuous fun y : E3 => spatFDeriv hm G y v := by
      simp only [spatFDeriv_apply]
      refine continuous_finset_sum _ fun j _ => ?_
      have hfun :
          (fun y : E3 => v j •
              (fourierInvBCF (two_le_pred_of_three hm)
                (dH (one_le_of_three hm) j G) y)) =
            fun y => (v j : ℂ) •
              (fourierInvBCF (two_le_pred_of_three hm)
                (dH (one_le_of_three hm) j G) y) :=
        funext fun y => real_smul_eq_coe_smul_V _ _
      rw [hfun]
      exact (continuous_const (y := (v j : ℂ))).smul
        (fourierInvBCF (two_le_pred_of_three hm)
          (dH (one_le_of_three hm) j G)).continuous
    exact hsp.comp hx
  have hint : IntervalIntegrable (fun t : ℝ => spatFDeriv hm G (x + t • v) v)
      volume 0 1 := hcont.intervalIntegrable 0 1
  have hconst : IntervalIntegrable (fun _ : ℝ => spatFDeriv hm G x v) volume 0 1 :=
    continuous_const.intervalIntegrable 0 1
  have hsub := intervalIntegral.integral_sub hint hconst
  have hc : (∫ _ in (0:ℝ)..1, spatFDeriv hm G x v) = spatFDeriv hm G x v := by
    simp [intervalIntegral.integral_const, one_smul]
  unfold uncurryFourierInvBCF
  rw [hFTC]
  change ((∫ t in (0:ℝ)..1, spatFDeriv hm G (x + t • v) v) -
      spatFDeriv hm G x v) =
    ∫ t in (0:ℝ)..1, spatFDerivDiff hm G x v t
  rw [← hc]
  simpa [spatFDerivDiff] using hsub.symm

lemma hasFDerivAt_uncurryFourierInvBCF {m : ℕ} (hm : 3 ≤ m) (x : E3) (G : Hm m) :
    HasFDerivAt (uncurryFourierInvBCF (two_le_of_three hm))
      (jointFDeriv hm x G) (x, G) := by
  refine hasFDerivAt_iff_isLittleO_nhds_zero.2 ?_
  rw [isLittleO_iff]
  intro ε hε
  let C : ℝ :=
    ∑ j : Fin 3,
      ‖(isBoundedLinearMap_fourierInvBCF
        (two_le_pred_of_three hm)).toContinuousLinearMap‖ *
        ‖(dH (one_le_of_three hm) j : Hm m →L[ℂ] Hm (m - 1))‖
  have hC0 : 0 ≤ C :=
    Finset.sum_nonneg fun j _ =>
      mul_nonneg
        (norm_nonneg
          (isBoundedLinearMap_fourierInvBCF
            (two_le_pred_of_three hm)).toContinuousLinearMap)
        (norm_nonneg
          (dH (one_le_of_three hm) j : Hm m →L[ℂ] Hm (m - 1)))
  have hbil : ∀ (H : Hm m) (v : E3),
      ‖spatFDeriv hm H x v‖ ≤ C * ‖H‖ * ‖v‖ :=
    fun H v => spatFDeriv_le_mul_norm hm H x v
  have hcontj : ∀ j, ContinuousAt
      (uncurryFourierInvBCF (two_le_pred_of_three hm))
      (x, dH (one_le_of_three hm) j G) :=
    fun j => (continuous_uncurryFourierInvBCF (two_le_pred_of_three hm)).continuousAt
  have hRadJ : ∀ j, ∃ radJ > 0, ∀ q : E3 × Hm (m - 1),
      dist q (x, dH (one_le_of_three hm) j G) < radJ →
        dist (uncurryFourierInvBCF (two_le_pred_of_three hm) q)
          (uncurryFourierInvBCF (two_le_pred_of_three hm)
            (x, dH (one_le_of_three hm) j G)) < ε / 12 := by
    intro j
    exact (Metric.continuousAt_iff).1 (hcontj j) (ε / 12)
      (div_pos hε (by norm_num : (0:ℝ) < 12))
  choose radJ hRadJpos hRadJuse using hRadJ
  let Mj : Fin 3 → ℝ := fun j =>
    ‖(dH (one_le_of_three hm) j : Hm m →L[ℂ] Hm (m - 1))‖ + 1
  have hMjpos : ∀ j, 0 < Mj j := fun j =>
    add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one
  let rad : ℝ :=
    min (ε / (2 * (C + 1)))
      (min (radJ 0 / Mj 0) (min (radJ 1 / Mj 1) (radJ 2 / Mj 2)))
  have hRadpos : 0 < rad := by
    refine lt_min ?_ (lt_min ?_ (lt_min ?_ ?_))
    · exact div_pos hε (mul_pos (by norm_num) (add_pos_of_nonneg_of_pos hC0 zero_lt_one))
    · exact div_pos (hRadJpos 0) (hMjpos 0)
    · exact div_pos (hRadJpos 1) (hMjpos 1)
    · exact div_pos (hRadJpos 2) (hMjpos 2)
  have hRadle_j : ∀ j, rad ≤ radJ j / Mj j := by
    intro j
    fin_cases j
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine Metric.eventually_nhds_iff.2 ⟨rad, hRadpos, ?_⟩
  intro p hp
  rcases p with ⟨v, H⟩
  have hpnorm : ‖(v, H)‖ < rad := by
    simpa [dist_eq_norm] using hp
  have hvle : ‖v‖ ≤ ‖(v, H)‖ := norm_fst_le (v, H)
  have hHle : ‖H‖ ≤ ‖(v, H)‖ := norm_snd_le (v, H)
  have hbilε : ‖spatFDeriv hm H x v‖ ≤ (ε / 2) * ‖(v, H)‖ := by
    have h1 : ‖spatFDeriv hm H x v‖ ≤ C * ‖H‖ * ‖v‖ := hbil H v
    have h2 : C * ‖H‖ * ‖v‖ ≤ C * ‖(v, H)‖ * ‖(v, H)‖ :=
      mul_le_mul (mul_le_mul_of_nonneg_left hHle hC0) hvle
        (norm_nonneg _) (mul_nonneg hC0 (norm_nonneg _))
    have hCδ : C * ‖(v, H)‖ ≤ ε / 2 := by
      have hRadle : ‖(v, H)‖ ≤ ε / (2 * (C + 1)) :=
        le_of_lt (hpnorm.trans_le (min_le_left _ _))
      have hdenpos : 0 < 2 * (C + 1) :=
        mul_pos (by norm_num) (add_pos_of_nonneg_of_pos hC0 zero_lt_one)
      calc
        C * ‖(v, H)‖ ≤ C * (ε / (2 * (C + 1))) :=
          mul_le_mul_of_nonneg_left hRadle hC0
        _ = (C / (C + 1)) * (ε / 2) := by
          field_simp
        _ ≤ (ε / 2) := by
          have hle : C / (C + 1) ≤ 1 :=
            (div_le_one (add_pos_of_nonneg_of_pos hC0 zero_lt_one)).2
              (le_add_of_nonneg_right zero_le_one)
          exact (mul_le_of_le_one_left (div_nonneg hε.le (by norm_num)) hle)
    have : C * ‖(v, H)‖ * ‖(v, H)‖ = (C * ‖(v, H)‖) * ‖(v, H)‖ := by ring
    rw [this] at h2
    exact h1.trans (h2.trans (mul_le_mul_of_nonneg_right hCδ (norm_nonneg _)))
  -- The two increment points stay inside each continuity ball.
  have hpts : ∀ t, t ∈ Set.Icc (0:ℝ) 1 → ∀ j,
      dist (x + t • v, dH (one_le_of_three hm) j (G + H))
        (x, dH (one_le_of_three hm) j G) < radJ j ∧
      dist (x, dH (one_le_of_three hm) j (G + H))
        (x, dH (one_le_of_three hm) j G) < radJ j := by
    intro t ht j
    have ht01 : 0 ≤ t ∧ t ≤ 1 := Set.mem_Icc.1 ht
    have htv : ‖t • v‖ ≤ ‖v‖ := by
      rw [norm_smul]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (abs_le.2 ⟨by linarith [ht01.1], ht01.2⟩)
    have hdHdiff :
        dH (one_le_of_three hm) j (G + H) - dH (one_le_of_three hm) j G =
          dH (one_le_of_three hm) j H := by
      simp [map_add]
    have hnD :
        ‖dH (one_le_of_three hm) j H‖ ≤
          ‖(dH (one_le_of_three hm) j : Hm m →L[ℂ] Hm (m - 1))‖ * ‖H‖ :=
      (dH (one_le_of_three hm) j).le_opNorm H
    have hscale : ‖(v, H)‖ < radJ j / Mj j :=
      hpnorm.trans_le (hRadle_j j)
    have hsmallD : ‖dH (one_le_of_three hm) j H‖ < radJ j := by
      have : ‖(dH (one_le_of_three hm) j : Hm m →L[ℂ] Hm (m - 1))‖ * ‖H‖ <
          Mj j * (radJ j / Mj j) :=
        mul_lt_mul' (le_add_of_nonneg_right zero_le_one)
          (lt_of_le_of_lt hHle hscale) (norm_nonneg _) (hMjpos j)
      have hMj : Mj j * (radJ j / Mj j) = radJ j := by
        field_simp [ne_of_gt (hMjpos j)]
      exact lt_of_le_of_lt hnD (this.trans_eq hMj)
    constructor
    · have h1 : dist (x + t • v) x ≤ ‖v‖ := by
        simpa [dist_eq_norm, add_sub_cancel_left] using htv
      have hvrad : ‖v‖ < radJ j :=
        (lt_of_le_of_lt hvle hscale).trans_le
          (div_le_self (le_of_lt (hRadJpos j))
            (show 1 ≤ Mj j from le_add_of_nonneg_left (norm_nonneg _)))
      rw [Prod.dist_eq, dist_eq_norm, dist_eq_norm, hdHdiff]
      exact max_lt (lt_of_le_of_lt h1 hvrad) hsmallD
    · rw [Prod.dist_eq]
      simp only [dist_eq_norm, sub_self, norm_zero, hdHdiff]
      simpa [max_eq_right (norm_nonneg _)] using hsmallD
  have hdiff : ∀ t ∈ Set.Icc (0:ℝ) 1,
      ‖spatFDerivDiff hm (G + H) x v t‖ ≤ (ε / 2) * ‖(v, H)‖ := by
    intro t ht
    have hcoord : ∀ j,
        ‖uncurryFourierInvBCF (two_le_pred_of_three hm)
              (x + t • v, dH (one_le_of_three hm) j (G + H)) -
            uncurryFourierInvBCF (two_le_pred_of_three hm)
              (x, dH (one_le_of_three hm) j (G + H))‖ < ε / 6 := by
      intro j
      have hA := hRadJuse j (x + t • v, dH (one_le_of_three hm) j (G + H))
        (hpts t ht j).1
      have hB := hRadJuse j (x, dH (one_le_of_three hm) j (G + H))
        (hpts t ht j).2
      have htri := dist_triangle_right
        (uncurryFourierInvBCF (two_le_pred_of_three hm)
          (x + t • v, dH (one_le_of_three hm) j (G + H)))
        (uncurryFourierInvBCF (two_le_pred_of_three hm)
          (x, dH (one_le_of_three hm) j (G + H)))
        (uncurryFourierInvBCF (two_le_pred_of_three hm)
          (x, dH (one_le_of_three hm) j G))
      have : dist
          (uncurryFourierInvBCF (two_le_pred_of_three hm)
            (x + t • v, dH (one_le_of_three hm) j (G + H)))
          (uncurryFourierInvBCF (two_le_pred_of_three hm)
            (x, dH (one_le_of_three hm) j (G + H))) < ε / 6 :=
        lt_of_le_of_lt htri ((add_lt_add hA hB).trans_eq (by ring))
      simpa [dist_eq_norm] using this
    have hle := norm_spatFDeriv_sub_le hm (G + H) (x + t • v) x v
    have : spatFDerivDiff hm (G + H) x v t =
        spatFDeriv hm (G + H) (x + t • v) v - spatFDeriv hm (G + H) x v := rfl
    rw [this]
    refine hle.trans ?_
    have hsum : (∑ j : Fin 3,
        ‖(fourierInvBCF (two_le_pred_of_three hm)
              (dH (one_le_of_three hm) j (G + H))).toFun (x + t • v) -
            (fourierInvBCF (two_le_pred_of_three hm)
              (dH (one_le_of_three hm) j (G + H))).toFun x‖) <
        3 * (ε / 6) := by
      have h3 : (∑ _j : Fin 3, ε / 6) = 3 * (ε / 6) := by
        simp
      refine (Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty) ?_).trans_eq h3
      intro j _
      have := hcoord j
      simpa [uncurryFourierInvBCF] using this
    have hsumle : (∑ j : Fin 3,
        ‖(fourierInvBCF (two_le_pred_of_three hm)
              (dH (one_le_of_three hm) j (G + H))).toFun (x + t • v) -
            (fourierInvBCF (two_le_pred_of_three hm)
              (dH (one_le_of_three hm) j (G + H))).toFun x‖) ≤
        ε / 2 := le_of_lt (hsum.trans_eq (by ring))
    exact (mul_le_mul_of_nonneg_left hsumle (norm_nonneg v)).trans
      (by
        have : ‖v‖ * (ε / 2) ≤ ‖(v, H)‖ * (ε / 2) :=
          mul_le_mul_of_nonneg_right hvle (div_nonneg hε.le (by norm_num))
        simpa [mul_comm] using this)
  have hinteg : ‖∫ t in (0:ℝ)..1, spatFDerivDiff hm (G + H) x v t‖ ≤
      (ε / 2) * ‖(v, H)‖ := by
    have hbound : ∀ t ∈ Set.uIoc (0:ℝ) 1,
        ‖spatFDerivDiff hm (G + H) x v t‖ ≤ (ε / 2) * ‖(v, H)‖ := by
      intro t ht
      have hsub : Set.uIoc (0:ℝ) 1 ⊆ Set.Icc 0 1 := by
        rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
        exact Set.Ioc_subset_Icc_self
      exact hdiff t (hsub ht)
    have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    simpa using this
  -- Assemble the two remainders.
  have heq :
      uncurryFourierInvBCF (two_le_of_three hm) (x + v, G + H) -
        uncurryFourierInvBCF (two_le_of_three hm) (x, G) -
        jointFDeriv hm x G (v, H) =
      (∫ t in (0:ℝ)..1, spatFDerivDiff hm (G + H) x v t) +
        spatFDeriv hm H x v := by
    rw [uncurryFourierInvBCF_remainder, spatial_remainder_eq_integral]
  have hfinal :
      ‖uncurryFourierInvBCF (two_le_of_three hm) (x + v, G + H) -
        uncurryFourierInvBCF (two_le_of_three hm) (x, G) -
        jointFDeriv hm x G (v, H)‖ ≤ ε * ‖(v, H)‖ := by
    have hsum := add_le_add hinteg hbilε
    have hεsum : ε / 2 * ‖(v, H)‖ + ε / 2 * ‖(v, H)‖ = ε * ‖(v, H)‖ := by ring
    rw [heq, ← hεsum]
    exact (norm_add_le _ _).trans hsum
  simpa [Prod.mk_add_mk] using hfinal

/-- Operator-norm constant in the bilinear bound for `spatFDeriv`. -/
def spatFDerivBound {m : ℕ} (hm : 3 ≤ m) : ℝ :=
  ∑ j : Fin 3,
    ‖(isBoundedLinearMap_fourierInvBCF
      (two_le_pred_of_three hm)).toContinuousLinearMap‖ *
      ‖(dH (one_le_of_three hm) j : Hm m →L[ℂ] Hm (m - 1))‖

lemma spatFDerivBound_nonneg {m : ℕ} (hm : 3 ≤ m) : 0 ≤ spatFDerivBound hm :=
  Finset.sum_nonneg fun j _ =>
    mul_nonneg
      (norm_nonneg
        (isBoundedLinearMap_fourierInvBCF
          (two_le_pred_of_three hm)).toContinuousLinearMap)
      (norm_nonneg (dH (one_le_of_three hm) j : Hm m →L[ℂ] Hm (m - 1)))

lemma spatFDeriv_le_bound {m : ℕ} (hm : 3 ≤ m) (G : Hm m) (x v : E3) :
    ‖spatFDeriv hm G x v‖ ≤ spatFDerivBound hm * ‖G‖ * ‖v‖ :=
  spatFDeriv_le_mul_norm hm G x v

/-- Sum of the operator norms of the first-order Fourier multipliers. -/
def dHBound {m : ℕ} (hm : 3 ≤ m) : ℝ :=
  ∑ j : Fin 3, ‖(dH (one_le_of_three hm) j : Hm m →L[ℂ] Hm (m - 1))‖

lemma dHBound_nonneg {m : ℕ} (hm : 3 ≤ m) : 0 ≤ dHBound hm :=
  Finset.sum_nonneg fun j _ =>
    norm_nonneg (dH (one_le_of_three hm) j : Hm m →L[ℂ] Hm (m - 1))

lemma spatFDeriv_add {m : ℕ} (hm : 3 ≤ m) (G H : Hm m) (x v : E3) :
    spatFDeriv hm (G + H) x v = spatFDeriv hm G x v + spatFDeriv hm H x v := by
  simp only [spatFDeriv_apply]
  have hadd := (isBoundedLinearMap_fourierInvBCF (two_le_pred_of_three hm)).map_add
  have hdH : ∀ j, dH (one_le_of_three hm) j (G + H) =
      dH (one_le_of_three hm) j G + dH (one_le_of_three hm) j H :=
    fun j => map_add _ _ _
  simp only [hdH, hadd, BoundedContinuousFunction.add_apply]
  refine Eq.trans (Finset.sum_congr rfl fun j _ => smul_add _ _ _) ?_
  exact Finset.sum_add_distrib

/-- The inverse Fourier transform is Lipschitz in the spatial variable,
uniformly on bounded sets of `Ĥ^m` (`m ≥ 3`). -/
lemma norm_fourierInvBCF_sub_le {m : ℕ} (hm : 3 ≤ m) (G : Hm m) (x y : E3) :
    ‖(fourierInvBCF (two_le_of_three hm) G).toFun x -
      (fourierInvBCF (two_le_of_three hm) G).toFun y‖ ≤
      spatFDerivBound hm * ‖G‖ * ‖x - y‖ := by
  have hFTC := fourierInvBCF_eq_integral_spatFDeriv hm G y (x - y)
  have hxy : y + (x - y) = x := add_sub_cancel y x
  rw [hxy] at hFTC
  have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖spatFDeriv hm G (y + t • (x - y)) (x - y)‖ ≤
        spatFDerivBound hm * ‖G‖ * ‖x - y‖ :=
    fun t _ => spatFDeriv_le_bound hm G _ (x - y)
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have habs : |(1 : ℝ) - 0| = 1 := by norm_num
  have hC : spatFDerivBound hm * ‖G‖ * ‖x - y‖ * |(1 : ℝ) - 0| =
      spatFDerivBound hm * ‖G‖ * ‖x - y‖ := by rw [habs, mul_one]
  exact (hFTC ▸ hI).trans_eq hC

lemma four_le {m : ℕ} (hm : 4 ≤ m) : 3 ≤ m :=
  le_trans (by norm_num : 3 ≤ 4) hm

lemma three_le_pred_of_four {m : ℕ} (hm : 4 ≤ m) : 3 ≤ m - 1 := by
  omega

/-- Operator-norm increment of the joint derivative, for `m ≥ 4`. -/
lemma norm_jointFDeriv_sub_le {m : ℕ} (hm : 4 ≤ m) (x y : E3) (G K : Hm m) :
    ‖jointFDeriv (four_le hm) x G - jointFDeriv (four_le hm) y K‖ ≤
      spatFDerivBound (four_le hm) * ‖G - K‖ +
        (spatFDerivBound (three_le_pred_of_four hm) *
          dHBound (four_le hm) * ‖K‖ +
          spatFDerivBound (four_le hm)) * ‖x - y‖ := by
  let hm3 := four_le hm
  let hpred := three_le_pred_of_four hm
  let C := spatFDerivBound hm3
  let C' := spatFDerivBound hpred
  let D := dHBound hm3
  have hC0 : 0 ≤ C := spatFDerivBound_nonneg hm3
  have hC'0 : 0 ≤ C' := spatFDerivBound_nonneg hpred
  have hD0 : 0 ≤ D := dHBound_nonneg hm3
  have hM0 : 0 ≤ C * ‖G - K‖ + (C' * D * ‖K‖ + C) * ‖x - y‖ :=
    add_nonneg (mul_nonneg hC0 (norm_nonneg _))
      (mul_nonneg (add_nonneg (mul_nonneg (mul_nonneg hC'0 hD0) (norm_nonneg _)) hC0)
        (norm_nonneg _))
  refine ContinuousLinearMap.opNorm_le_bound _ hM0 ?_
  intro p
  rcases p with ⟨v, H⟩
  have hsplit :
      jointFDeriv hm3 x G (v, H) - jointFDeriv hm3 y K (v, H) =
        spatFDeriv hm3 (G - K) x v +
          (spatFDeriv hm3 K x v - spatFDeriv hm3 K y v) +
          ((fourierInvBCF (two_le_of_three hm3) H).toFun x -
            (fourierInvBCF (two_le_of_three hm3) H).toFun y) := by
    have hadd := spatFDeriv_add hm3 (G - K) K x v
    have hGK : G - K + K = G := sub_add_cancel G K
    rw [hGK] at hadd
    rw [jointFDeriv_apply, jointFDeriv_apply, hadd]
    abel
  have h1 : ‖spatFDeriv hm3 (G - K) x v‖ ≤ C * ‖G - K‖ * ‖v‖ :=
    spatFDeriv_le_bound hm3 (G - K) x v
  have h3 : ‖(fourierInvBCF (two_le_of_three hm3) H).toFun x -
      (fourierInvBCF (two_le_of_three hm3) H).toFun y‖ ≤
      C * ‖H‖ * ‖x - y‖ :=
    norm_fourierInvBCF_sub_le hm3 H x y
  have h2 : ‖spatFDeriv hm3 K x v - spatFDeriv hm3 K y v‖ ≤
      C' * D * ‖K‖ * ‖x - y‖ * ‖v‖ := by
    refine (norm_spatFDeriv_sub_le hm3 K x y v).trans ?_
    have hsum :
        (∑ j : Fin 3,
          ‖(fourierInvBCF (two_le_pred_of_three hm3)
              (dH (one_le_of_three hm3) j K)).toFun x -
            (fourierInvBCF (two_le_pred_of_three hm3)
              (dH (one_le_of_three hm3) j K)).toFun y‖) ≤
          C' * D * ‖K‖ * ‖x - y‖ := by
      have hterm : ∀ j,
          ‖(fourierInvBCF (two_le_pred_of_three hm3)
              (dH (one_le_of_three hm3) j K)).toFun x -
            (fourierInvBCF (two_le_pred_of_three hm3)
              (dH (one_le_of_three hm3) j K)).toFun y‖ ≤
            C' * ‖(dH (one_le_of_three hm3) j : Hm m →L[ℂ] Hm (m - 1))‖ * ‖K‖ *
              ‖x - y‖ := by
        intro j
        have hlip :=
          norm_fourierInvBCF_sub_le hpred
            (dH (one_le_of_three hm3) j K) x y
        have hop :
            ‖(dH (one_le_of_three hm3) j : Hm m →L[ℂ] Hm (m - 1)) K‖ ≤
              ‖(dH (one_le_of_three hm3) j : Hm m →L[ℂ] Hm (m - 1))‖ * ‖K‖ :=
          ContinuousLinearMap.le_opNorm _ _
        refine hlip.trans ?_
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hop hC'0) (norm_nonneg (x - y))
        simpa [mul_assoc] using this
      refine (Finset.sum_le_sum fun j _ => hterm j).trans ?_
      have hfac :
          (∑ j : Fin 3,
            C' * ‖(dH (one_le_of_three hm3) j : Hm m →L[ℂ] Hm (m - 1))‖ * ‖K‖ *
              ‖x - y‖) =
            C' * D * ‖K‖ * ‖x - y‖ := by
        calc
          (∑ j : Fin 3,
              C' * ‖(dH (one_le_of_three hm3) j : Hm m →L[ℂ] Hm (m - 1))‖ * ‖K‖ *
                ‖x - y‖)
              = C' * (∑ j : Fin 3,
                  ‖(dH (one_le_of_three hm3) j : Hm m →L[ℂ] Hm (m - 1))‖) *
                (‖K‖ * ‖x - y‖) := by
            simp only [mul_assoc, ← Finset.mul_sum]
            congr 1
            exact (Finset.sum_mul _ _ _).symm
          _ = C' * D * ‖K‖ * ‖x - y‖ := by
            simp [D, dHBound, mul_assoc]
      exact le_of_eq hfac
    have hmul : ‖v‖ * (C' * D * ‖K‖ * ‖x - y‖) = C' * D * ‖K‖ * ‖x - y‖ * ‖v‖ := by
      ring
    exact (mul_le_mul_of_nonneg_left hsum (norm_nonneg v)).trans_eq hmul
  have hv : ‖v‖ ≤ ‖(v, H)‖ := norm_fst_le (v, H)
  have hH : ‖H‖ ≤ ‖(v, H)‖ := norm_snd_le (v, H)
  have h1' : ‖spatFDeriv hm3 (G - K) x v‖ ≤ C * ‖G - K‖ * ‖(v, H)‖ :=
    h1.trans (mul_le_mul_of_nonneg_left hv (mul_nonneg hC0 (norm_nonneg _)))
  have h3' :
      ‖(fourierInvBCF (two_le_of_three hm3) H).toFun x -
        (fourierInvBCF (two_le_of_three hm3) H).toFun y‖ ≤
        C * ‖x - y‖ * ‖(v, H)‖ := by
    have hstep : C * ‖H‖ * ‖x - y‖ ≤ C * ‖(v, H)‖ * ‖x - y‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hH hC0) (norm_nonneg (x - y))
    have := h3.trans hstep
    convert this using 1
    ring
  have h2'' : ‖spatFDeriv hm3 K x v - spatFDeriv hm3 K y v‖ ≤
      C' * D * ‖K‖ * ‖x - y‖ * ‖(v, H)‖ :=
    h2.trans (mul_le_mul_of_nonneg_left hv
      (mul_nonneg (mul_nonneg (mul_nonneg hC'0 hD0) (norm_nonneg K))
        (norm_nonneg (x - y))))
  have hsum :=
    (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h1' h2'')) h3')
  rw [ContinuousLinearMap.sub_apply, hsplit]
  refine hsum.trans ?_
  have : C * ‖G - K‖ * ‖(v, H)‖ + C' * D * ‖K‖ * ‖x - y‖ * ‖(v, H)‖ +
      C * ‖x - y‖ * ‖(v, H)‖ =
      (C * ‖G - K‖ + (C' * D * ‖K‖ + C) * ‖x - y‖) * ‖(v, H)‖ := by
    ring
  exact le_of_eq this

/-- The joint derivative is continuous as a map into operators, for `m ≥ 4`. -/
lemma continuous_jointFDeriv {m : ℕ} (hm : 4 ≤ m) :
    Continuous (fun p : E3 × Hm m => jointFDeriv (four_le hm) p.1 p.2) := by
  refine Metric.continuous_iff.2 ?_
  intro p ε hε
  let x0 := p.1
  let G0 := p.2
  let C := spatFDerivBound (four_le hm)
  let C' := spatFDerivBound (three_le_pred_of_four hm)
  let D := dHBound (four_le hm)
  let A := C + (C' * D * ‖G0‖ + C)
  have hA0 : 0 ≤ A :=
    add_nonneg (spatFDerivBound_nonneg _)
      (add_nonneg (mul_nonneg (mul_nonneg (spatFDerivBound_nonneg _) (dHBound_nonneg _))
        (norm_nonneg _)) (spatFDerivBound_nonneg _))
  have hA1 : 0 < A + 1 := lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left hA0)
  refine ⟨ε / (A + 1), div_pos hε hA1, ?_⟩
  intro q hq
  have hdist : ‖q - p‖ < ε / (A + 1) := by
    simpa [dist_eq_norm] using hq
  have hx : ‖q.1 - x0‖ ≤ ‖q - p‖ := by
    change ‖q.1 - p.1‖ ≤ ‖q - p‖
    rw [Prod.norm_def]
    exact le_max_left _ _
  have hG : ‖q.2 - G0‖ ≤ ‖q - p‖ := by
    change ‖q.2 - p.2‖ ≤ ‖q - p‖
    rw [Prod.norm_def]
    exact le_max_right _ _
  have hle := norm_jointFDeriv_sub_le hm q.1 x0 q.2 G0
  have hbound :
      ‖jointFDeriv (four_le hm) q.1 q.2 - jointFDeriv (four_le hm) x0 G0‖ ≤
        A * ‖q - p‖ := by
    refine hle.trans ?_
    have : C * ‖q.2 - G0‖ + (C' * D * ‖G0‖ + C) * ‖q.1 - x0‖ ≤
        C * ‖q - p‖ + (C' * D * ‖G0‖ + C) * ‖q - p‖ :=
      add_le_add
        (mul_le_mul_of_nonneg_left hG (spatFDerivBound_nonneg _))
        (mul_le_mul_of_nonneg_left hx
          (add_nonneg (mul_nonneg (mul_nonneg (spatFDerivBound_nonneg _) (dHBound_nonneg _))
            (norm_nonneg _)) (spatFDerivBound_nonneg _)))
    simpa [A, mul_add, add_mul] using this
  have hlt : A * ‖q - p‖ < A * (ε / (A + 1)) ∨ A = 0 := by
    by_cases hA : A = 0
    · exact Or.inr hA
    · exact Or.inl (mul_lt_mul_of_pos_left hdist (lt_of_le_of_ne hA0 (Ne.symm hA)))
  have hfinal : A * ‖q - p‖ < ε := by
    cases hlt with
    | inl hlt =>
      have : A * (ε / (A + 1)) = (A / (A + 1)) * ε := by field_simp
      have hfrac : A / (A + 1) < 1 :=
        (div_lt_one hA1).2 (lt_add_one A)
      exact hlt.trans_le (by rw [this]; exact (mul_le_of_le_one_left (le_of_lt hε)
        (le_of_lt hfrac)))
    | inr hA =>
      simp [hA, hε]
  have : dist (jointFDeriv (four_le hm) q.1 q.2)
      (jointFDeriv (four_le hm) p.1 p.2) < ε := by
    simpa [dist_eq_norm, x0, G0] using (hbound.trans_lt hfinal)
  exact this

lemma fderiv_uncurryFourierInvBCF {m : ℕ} (hm : 3 ≤ m) (x : E3) (G : Hm m) :
    fderiv ℝ (uncurryFourierInvBCF (two_le_of_three hm)) (x, G) =
      jointFDeriv hm x G :=
  (hasFDerivAt_uncurryFourierInvBCF hm x G).fderiv

lemma differentiable_uncurryFourierInvBCF {m : ℕ} (hm : 3 ≤ m) :
    Differentiable ℝ (uncurryFourierInvBCF (two_le_of_three hm)) :=
  fun p => (hasFDerivAt_uncurryFourierInvBCF hm p.1 p.2).differentiableAt

/-- The uncurried inverse Fourier transform is jointly `C¹` on `ℝ³ × Ĥ^m` for `m ≥ 4`. -/
theorem contDiff_one_uncurryFourierInvBCF {m : ℕ} (hm : 4 ≤ m) :
    ContDiff ℝ 1 (uncurryFourierInvBCF (two_le_of_three (four_le hm))) := by
  refine contDiff_one_iff_fderiv.2 ⟨differentiable_uncurryFourierInvBCF (four_le hm), ?_⟩
  have hfun :
      fderiv ℝ (uncurryFourierInvBCF (two_le_of_three (four_le hm))) =
        fun p => jointFDeriv (four_le hm) p.1 p.2 :=
    funext fun p => fderiv_uncurryFourierInvBCF (four_le hm) p.1 p.2
  exact hfun ▸ continuous_jointFDeriv hm

/-- Post-composing the uncurried inverse Fourier transform with a `C¹` path
in `Ĥ^m` (`m ≥ 4`) yields a jointly `C¹` field on `ℝ³ × [0, T)`, including
the one-sided time derivative at `t = 0`. -/
theorem contDiffOn_uncurryFourierInvBCF_path {m : ℕ} (hm : 4 ≤ m)
    {T : ℝ} {γ : ℝ → Hm m} (hγ : ContDiffOn ℝ 1 γ (Ico 0 T)) :
    ContDiffOn ℝ 1
      (fun q : E3 × ℝ =>
        uncurryFourierInvBCF (two_le_of_three (four_le hm)) (q.1, γ q.2))
      (univ ×ˢ Ico 0 T) := by
  have hΦ : ContDiff ℝ 1
      (uncurryFourierInvBCF (two_le_of_three (four_le hm))) :=
    contDiff_one_uncurryFourierInvBCF hm
  have hpath : ContDiffOn ℝ 1 (fun q : E3 × ℝ => (q.1, γ q.2))
      (univ ×ˢ Ico 0 T) :=
    ContDiffOn.prodMk contDiff_fst.contDiffOn
      (hγ.comp contDiffOn_snd fun q hq => hq.2)
  exact hΦ.comp_contDiffOn hpath

/-- The same joint `C¹` regularity after post-composing with a continuous
linear map (e.g. taking real parts). -/
theorem contDiffOn_uncurry_clm_fourierInvBCF_one {m : ℕ} (hm : 4 ≤ m)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : V →L[ℝ] F)
    {T : ℝ} {γ : ℝ → Hm m} (hγ : ContDiffOn ℝ 1 γ (Ico 0 T)) :
    ContDiffOn ℝ 1 (fun q : E3 × ℝ =>
      L (uncurryFourierInvBCF (two_le_of_three (four_le hm)) (q.1, γ q.2)))
      (univ ×ˢ Ico 0 T) :=
  L.contDiff.comp_contDiffOn (contDiffOn_uncurryFourierInvBCF_path hm hγ)

/-- Evaluation of the inverse Fourier transform in the representative, as a
map from the spatial variable into operators `Ĥ^m →L ℂ³`. -/
def evMap {m : ℕ} (hm : 2 ≤ m) (x : E3) : Hm m →L[ℝ] V :=
  (evalCLM (𝕜 := ℝ) x).comp
    (isBoundedLinearMap_fourierInvBCF hm).toContinuousLinearMap

lemma evMap_apply {m : ℕ} (hm : 2 ≤ m) (x : E3) (H : Hm m) :
    evMap hm x H = uncurryFourierInvBCF hm (x, H) :=
  rfl

lemma spatFDeriv_smul {m : ℕ} (hm : 3 ≤ m) (c : ℝ) (G : Hm m) (x v : E3) :
    spatFDeriv hm (c • G) x v = c • spatFDeriv hm G x v := by
  simp only [spatFDeriv_apply]
  have hreal : ∀ j, dH (one_le_of_three hm) j (c • G) =
      c • dH (one_le_of_three hm) j G := by
    intro j
    have hcoe : (c • G : Hm m) = (c : ℂ) • G := real_smul_eq_coe_smul c G
    have hcoe' : (c • dH (one_le_of_three hm) j G : Hm (m - 1)) =
        (c : ℂ) • dH (one_le_of_three hm) j G :=
      real_smul_eq_coe_smul c _
    have hlin : dH (one_le_of_three hm) j ((c : ℂ) • G) =
        (c : ℂ) • dH (one_le_of_three hm) j G :=
      map_smul _ _ _
    exact (congrArg (dH (one_le_of_three hm) j) hcoe).trans (hlin.trans hcoe'.symm)
  have hsmul := (isBoundedLinearMap_fourierInvBCF (two_le_pred_of_three hm)).map_smul
  calc
    ∑ j : Fin 3, v j •
          (fourierInvBCF (two_le_pred_of_three hm)
            (dH (one_le_of_three hm) j (c • G)) x)
        = ∑ j : Fin 3, v j •
            (fourierInvBCF (two_le_pred_of_three hm)
              (c • dH (one_le_of_three hm) j G) x) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hreal j]
    _ = ∑ j : Fin 3, v j •
          (c • fourierInvBCF (two_le_pred_of_three hm)
            (dH (one_le_of_three hm) j G) x) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hsmul, BoundedContinuousFunction.smul_apply]; rfl
    _ = ∑ j : Fin 3, c •
          (v j • fourierInvBCF (two_le_pred_of_three hm)
            (dH (one_le_of_three hm) j G) x) :=
          Finset.sum_congr rfl fun j _ =>
            smul_comm (v j) c
              (fourierInvBCF (two_le_pred_of_three hm)
                (dH (one_le_of_three hm) j G) x)
    _ = c • ∑ j : Fin 3, v j •
          fourierInvBCF (two_le_pred_of_three hm)
            (dH (one_le_of_three hm) j G) x :=
          (Finset.smul_sum).symm

/-- `G ↦ spatFDeriv G x` is a bounded linear map into operators on `ℝ³`. -/
lemma isBoundedLinearMap_spatFDeriv {m : ℕ} (hm : 3 ≤ m) (x : E3) :
    IsBoundedLinearMap ℝ (fun G : Hm m => spatFDeriv hm G x) where
  map_add := by
    intro G H
    exact ContinuousLinearMap.ext fun v => spatFDeriv_add hm G H x v
  map_smul := by
    intro c G
    exact ContinuousLinearMap.ext fun v => spatFDeriv_smul hm c G x v
  bound := by
    refine ⟨max (spatFDerivBound hm) 1,
      lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun G => ?_⟩
    have h : ‖spatFDeriv hm G x‖ ≤ spatFDerivBound hm * ‖G‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (spatFDerivBound_nonneg hm)
        (norm_nonneg G)) ?_
      intro v
      have := spatFDeriv_le_bound hm G x v
      simpa [mul_assoc] using this
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg G))

/-- Operator-norm Lipschitz estimate for `spatFDeriv` in the spatial variable,
for `m ≥ 4`. -/
lemma norm_spatFDeriv_sub_op {m : ℕ} (hm : 4 ≤ m) (H : Hm m) (x y : E3) :
    ‖spatFDeriv (four_le hm) H x - spatFDeriv (four_le hm) H y‖ ≤
      spatFDerivBound (three_le_pred_of_four hm) *
        dHBound (four_le hm) * ‖H‖ * ‖x - y‖ := by
  let hm3 := four_le hm
  let hpred := three_le_pred_of_four hm
  let C' := spatFDerivBound hpred
  let D := dHBound hm3
  have hC'0 : 0 ≤ C' := spatFDerivBound_nonneg hpred
  have hM0 : 0 ≤ C' * D * ‖H‖ * ‖x - y‖ :=
    mul_nonneg (mul_nonneg (mul_nonneg hC'0 (dHBound_nonneg hm3)) (norm_nonneg H))
      (norm_nonneg (x - y))
  refine ContinuousLinearMap.opNorm_le_bound _ hM0 ?_
  intro v
  refine (norm_spatFDeriv_sub_le hm3 H x y v).trans ?_
  have hterm : ∀ j,
      ‖(fourierInvBCF (two_le_pred_of_three hm3)
          (dH (one_le_of_three hm3) j H)).toFun x -
        (fourierInvBCF (two_le_pred_of_three hm3)
          (dH (one_le_of_three hm3) j H)).toFun y‖ ≤
        C' * ‖(dH (one_le_of_three hm3) j : Hm m →L[ℂ] Hm (m - 1))‖ * ‖H‖ *
          ‖x - y‖ := by
    intro j
    have hlip := norm_fourierInvBCF_sub_le hpred (dH (one_le_of_three hm3) j H) x y
    have hop :
        ‖(dH (one_le_of_three hm3) j : Hm m →L[ℂ] Hm (m - 1)) H‖ ≤
          ‖(dH (one_le_of_three hm3) j : Hm m →L[ℂ] Hm (m - 1))‖ * ‖H‖ :=
      ContinuousLinearMap.le_opNorm _ _
    refine hlip.trans ?_
    have := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hop hC'0) (norm_nonneg (x - y))
    simpa [mul_assoc] using this
  have hsum :
      (∑ j : Fin 3,
        ‖(fourierInvBCF (two_le_pred_of_three hm3)
            (dH (one_le_of_three hm3) j H)).toFun x -
          (fourierInvBCF (two_le_pred_of_three hm3)
            (dH (one_le_of_three hm3) j H)).toFun y‖) ≤
        C' * D * ‖H‖ * ‖x - y‖ := by
    have hsum0 :=
      Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => hterm j
    refine hsum0.trans (le_of_eq ?_)
    calc
      (∑ j : Fin 3,
          C' * ‖(dH (one_le_of_three hm3) j : Hm m →L[ℂ] Hm (m - 1))‖ * ‖H‖ *
            ‖x - y‖)
          = C' * (∑ j : Fin 3,
              ‖(dH (one_le_of_three hm3) j : Hm m →L[ℂ] Hm (m - 1))‖) *
            (‖H‖ * ‖x - y‖) := by
        simp only [mul_assoc, ← Finset.mul_sum]
        congr 1
        exact (Finset.sum_mul _ _ _).symm
      _ = C' * D * ‖H‖ * ‖x - y‖ := by
        simp [D, dHBound, mul_assoc]
  have hmul : ‖v‖ * (C' * D * ‖H‖ * ‖x - y‖) = C' * D * ‖H‖ * ‖x - y‖ * ‖v‖ := by
    ring
  exact (mul_le_mul_of_nonneg_left hsum (norm_nonneg v)).trans_eq hmul

/-- The candidate derivative of `evMap` at `x`. -/
def evFDeriv {m : ℕ} (hm : 3 ≤ m) (x : E3) : E3 →L[ℝ] (Hm m →L[ℝ] V) :=
  (isBoundedLinearMap_spatFDeriv hm x).toContinuousLinearMap.flip

lemma evFDeriv_apply {m : ℕ} (hm : 3 ≤ m) (x ξ : E3) (H : Hm m) :
    evFDeriv hm x ξ H = spatFDeriv hm H x ξ :=
  rfl

lemma norm_spatFDerivDiff_le {m : ℕ} (hm : 4 ≤ m) (H : Hm m) (x ξ : E3) {t : ℝ}
    (ht : t ∈ Set.uIoc (0 : ℝ) 1) :
    ‖spatFDerivDiff (four_le hm) H x ξ t‖ ≤
      spatFDerivBound (three_le_pred_of_four hm) * dHBound (four_le hm) *
        ‖H‖ * ‖ξ‖ * ‖ξ‖ := by
  have hu : Set.uIoc (0 : ℝ) 1 = Ioc 0 1 := Set.uIoc_of_le (by norm_num)
  have htI : t ∈ Icc (0 : ℝ) 1 :=
    Ioc_subset_Icc_self (by rwa [hu] at ht)
  have htabs : |t| ≤ 1 :=
    abs_le.2 ⟨le_trans (by norm_num : (-1 : ℝ) ≤ 0) htI.1, htI.2⟩
  unfold spatFDerivDiff
  have hop :=
    ContinuousLinearMap.le_opNorm
      (spatFDeriv (four_le hm) H (x + t • ξ) - spatFDeriv (four_le hm) H x) ξ
  have hsub := norm_spatFDeriv_sub_op hm H (x + t • ξ) x
  have hC'0 : 0 ≤ spatFDerivBound (three_le_pred_of_four hm) :=
    spatFDerivBound_nonneg _
  have hD0 : 0 ≤ dHBound (four_le hm) := dHBound_nonneg (four_le hm)
  have h1 :
      ‖spatFDeriv (four_le hm) H (x + t • ξ) ξ - spatFDeriv (four_le hm) H x ξ‖ ≤
        spatFDerivBound (three_le_pred_of_four hm) * dHBound (four_le hm) *
          ‖H‖ * (|t| * ‖ξ‖) * ‖ξ‖ := by
    have h0 := hop.trans (mul_le_mul_of_nonneg_right hsub (norm_nonneg ξ))
    have hx : (x + t • ξ) - x = t • ξ := add_sub_cancel_left _ _
    have hts : ‖t • ξ‖ = |t| * ‖ξ‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    simpa [hx, hts, mul_assoc] using h0
  have h2 :
      spatFDerivBound (three_le_pred_of_four hm) * dHBound (four_le hm) *
          ‖H‖ * (|t| * ‖ξ‖) * ‖ξ‖ ≤
        spatFDerivBound (three_le_pred_of_four hm) * dHBound (four_le hm) *
          ‖H‖ * (1 * ‖ξ‖) * ‖ξ‖ := by
    have htsle : |t| * ‖ξ‖ ≤ 1 * ‖ξ‖ :=
      mul_le_mul_of_nonneg_right htabs (norm_nonneg ξ)
    have hnn : 0 ≤ spatFDerivBound (three_le_pred_of_four hm) * dHBound (four_le hm) *
        ‖H‖ :=
      mul_nonneg (mul_nonneg hC'0 hD0) (norm_nonneg H)
    have hmid := mul_le_mul_of_nonneg_left htsle hnn
    exact mul_le_mul_of_nonneg_right hmid (norm_nonneg ξ)
  have h3 :
      spatFDerivBound (three_le_pred_of_four hm) * dHBound (four_le hm) *
          ‖H‖ * (1 * ‖ξ‖) * ‖ξ‖ =
        spatFDerivBound (three_le_pred_of_four hm) * dHBound (four_le hm) *
          ‖H‖ * ‖ξ‖ * ‖ξ‖ := by
    ring
  exact h1.trans (h2.trans (le_of_eq h3))

/-- `evMap` is Fréchet differentiable for `m ≥ 4`, with derivative `evFDeriv`. -/
lemma hasFDerivAt_evMap {m : ℕ} (hm : 4 ≤ m) (x : E3) :
    HasFDerivAt (evMap (two_le_of_three (four_le hm)))
      (evFDeriv (four_le hm) x) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro ε hε
  let hm3 := four_le hm
  let A := spatFDerivBound (three_le_pred_of_four hm) * dHBound hm3
  have hA0 : 0 ≤ A :=
    mul_nonneg (spatFDerivBound_nonneg _) (dHBound_nonneg hm3)
  have hA1 : 0 < A + 1 := lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left hA0)
  let rad := ε / (A + 1)
  have hrad : 0 < rad := div_pos hε hA1
  refine Metric.eventually_nhds_iff.2 ⟨rad, hrad, ?_⟩
  intro ξ hξ
  have hξn : ‖ξ‖ < rad := by
    simpa [dist_eq_norm, sub_zero] using hξ
  have hbound : ∀ H : Hm m,
      ‖evMap (two_le_of_three hm3) (x + ξ) H -
        evMap (two_le_of_three hm3) x H -
        evFDeriv hm3 x ξ H‖ ≤
        A * ‖ξ‖ * ‖ξ‖ * ‖H‖ := by
    intro H
    have heq := spatial_remainder_eq_integral hm3 H x ξ
    have hlip : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ‖spatFDerivDiff hm3 H x ξ t‖ ≤ A * ‖H‖ * ‖ξ‖ * ‖ξ‖ := by
      intro t ht
      have := norm_spatFDerivDiff_le hm H x ξ ht
      simpa [A, mul_assoc, mul_left_comm, mul_comm] using this
    have hI := intervalIntegral.norm_integral_le_of_norm_le_const hlip
    have habs : A * ‖H‖ * ‖ξ‖ * ‖ξ‖ * |(1 : ℝ) - 0| = A * ‖ξ‖ * ‖ξ‖ * ‖H‖ := by
      norm_num
      ring
    exact (heq ▸ hI).trans (le_of_eq habs)
  have hop : ‖evMap (two_le_of_three hm3) (x + ξ) -
      evMap (two_le_of_three hm3) x -
      evFDeriv hm3 x ξ‖ ≤ A * ‖ξ‖ * ‖ξ‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (mul_nonneg hA0 (norm_nonneg ξ)) (norm_nonneg ξ)) ?_
    intro H
    have := hbound H
    simpa [ContinuousLinearMap.sub_apply] using this
  have hfinal : A * ‖ξ‖ * ‖ξ‖ ≤ ε * ‖ξ‖ := by
    by_cases h0 : ξ = 0
    · simp [h0]
    · have : A * ‖ξ‖ ≤ A * rad :=
        mul_le_mul_of_nonneg_left (le_of_lt hξn) hA0
      have hstep : A * ‖ξ‖ * ‖ξ‖ ≤ (A * rad) * ‖ξ‖ :=
        mul_le_mul_of_nonneg_right this (norm_nonneg ξ)
      refine hstep.trans ?_
      have : A * rad * ‖ξ‖ = (A / (A + 1)) * ε * ‖ξ‖ := by
        unfold rad
        field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_left (le_of_lt hε)
          ((div_le_one hA1).2 (le_add_of_nonneg_right zero_le_one)))
        (norm_nonneg ξ)
  exact hop.trans hfinal

lemma fderiv_evMap {m : ℕ} (hm : 4 ≤ m) (x : E3) :
    fderiv ℝ (evMap (two_le_of_three (four_le hm))) x = evFDeriv (four_le hm) x :=
  (hasFDerivAt_evMap hm x).fderiv

lemma differentiable_evMap {m : ℕ} (hm : 4 ≤ m) :
    Differentiable ℝ (evMap (two_le_of_three (four_le hm))) :=
  fun x => (hasFDerivAt_evMap hm x).differentiableAt

/-- Operator-norm Lipschitz estimate for `evFDeriv` in the spatial variable. -/
lemma norm_evFDeriv_sub_le {m : ℕ} (hm : 4 ≤ m) (x y : E3) :
    ‖evFDeriv (four_le hm) y - evFDeriv (four_le hm) x‖ ≤
      spatFDerivBound (three_le_pred_of_four hm) * dHBound (four_le hm) * ‖y - x‖ := by
  let A := spatFDerivBound (three_le_pred_of_four hm) * dHBound (four_le hm)
  have hA0 : 0 ≤ A :=
    mul_nonneg (spatFDerivBound_nonneg _) (dHBound_nonneg (four_le hm))
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hA0 (norm_nonneg (y - x))) ?_
  intro ξ
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg hA0 (norm_nonneg (y - x))) (norm_nonneg ξ)) ?_
  intro H
  have hop :=
    ContinuousLinearMap.le_opNorm
      (spatFDeriv (four_le hm) H y - spatFDeriv (four_le hm) H x) ξ
  have hsub := norm_spatFDeriv_sub_op hm H y x
  have h1 : ‖spatFDeriv (four_le hm) H y ξ - spatFDeriv (four_le hm) H x ξ‖ ≤
      A * ‖H‖ * ‖y - x‖ * ‖ξ‖ := by
    have h0 := hop.trans (mul_le_mul_of_nonneg_right hsub (norm_nonneg ξ))
    have : spatFDerivBound (three_le_pred_of_four hm) * dHBound (four_le hm) *
        ‖H‖ * ‖y - x‖ * ‖ξ‖ = A * ‖H‖ * ‖y - x‖ * ‖ξ‖ := by
      simp [A, mul_assoc]
    exact h0.trans (le_of_eq this)
  have hgoal :
      ‖(evFDeriv (four_le hm) y - evFDeriv (four_le hm) x) ξ H‖ ≤
        A * ‖y - x‖ * ‖ξ‖ * ‖H‖ := by
    simpa [evFDeriv_apply, ContinuousLinearMap.sub_apply] using
      (h1.trans (le_of_eq (by ring)))
  exact hgoal

lemma continuous_evFDeriv {m : ℕ} (hm : 4 ≤ m) :
    Continuous (evFDeriv (four_le hm) :
      E3 → (E3 →L[ℝ] (Hm m →L[ℝ] V))) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  refine (tendsto_iff_norm_sub_tendsto_zero
      (E := E3 →L[ℝ] (Hm m →L[ℝ] V))
      (f := (evFDeriv (four_le hm) : E3 → (E3 →L[ℝ] (Hm m →L[ℝ] V))))
      (b := evFDeriv (four_le hm) x)).2 ?_
  let A := spatFDerivBound (three_le_pred_of_four hm) * dHBound (four_le hm)
  have hle : ∀ y : E3,
      ‖evFDeriv (four_le hm) y - evFDeriv (four_le hm) x‖ ≤ A * ‖y - x‖ :=
    fun y => norm_evFDeriv_sub_le hm x y
  have h0 : Tendsto (fun y : E3 => A * ‖y - x‖) (𝓝 x) (𝓝 0) := by
    have hnorm : Tendsto (fun y : E3 => ‖y - x‖) (𝓝 x) (𝓝 0) :=
      tendsto_norm_sub_self x
    have hmul := (tendsto_const_nhds (x := A)).mul hnorm
    simpa using hmul
  exact squeeze_zero
    (fun y => norm_nonneg (evFDeriv (four_le hm) y - evFDeriv (four_le hm) x))
    hle h0

/-- Evaluation in the representative is `C¹` in the spatial variable, for `m ≥ 4`. -/
theorem contDiff_one_evMap {m : ℕ} (hm : 4 ≤ m) :
    ContDiff ℝ 1 (evMap (two_le_of_three (four_le hm))) := by
  refine contDiff_one_iff_fderiv.2 ⟨differentiable_evMap hm, ?_⟩
  have hfun : fderiv ℝ (evMap (two_le_of_three (four_le hm))) =
      evFDeriv (four_le hm) :=
    funext fun x => fderiv_evMap hm x
  exact hfun ▸ continuous_evFDeriv hm

#print axioms FourierInvFDeriv.spatFDeriv_apply
#print axioms FourierInvFDeriv.coeFn_sum_dH
#print axioms FourierInvFDeriv.fourierInv_sum_smul
#print axioms FourierInvFDeriv.fourier_clm_apply
#print axioms FourierInvFDeriv.integrable_fourierSMulRight
#print axioms FourierInvFDeriv.fourierSMulRight_comp_neg_apply
#print axioms FourierInvFDeriv.integrable_comp_neg_of_Hm
#print axioms FourierInvFDeriv.spatFDeriv_apply_eq
#print axioms FourierInvFDeriv.hasFDerivAt_fourierInvBCF
#print axioms FourierInvFDeriv.continuous_uncurryFourierInvBCF
#print axioms FourierInvFDeriv.jointFDeriv_apply
#print axioms FourierInvFDeriv.norm_spatFDeriv_le
#print axioms FourierInvFDeriv.fourierInvBCF_eq_integral_spatFDeriv
#print axioms FourierInvFDeriv.spatFDeriv_le_mul_norm
#print axioms FourierInvFDeriv.uncurryFourierInvBCF_add
#print axioms FourierInvFDeriv.uncurryFourierInvBCF_remainder
#print axioms FourierInvFDeriv.norm_spatFDeriv_sub_le
#print axioms FourierInvFDeriv.spatial_remainder_eq_integral
#print axioms FourierInvFDeriv.hasFDerivAt_uncurryFourierInvBCF
#print axioms FourierInvFDeriv.norm_fourierInvBCF_sub_le
#print axioms FourierInvFDeriv.norm_jointFDeriv_sub_le
#print axioms FourierInvFDeriv.continuous_jointFDeriv
#print axioms FourierInvFDeriv.contDiff_one_uncurryFourierInvBCF
#print axioms FourierInvFDeriv.contDiffOn_uncurryFourierInvBCF_path
#print axioms FourierInvFDeriv.contDiffOn_uncurry_clm_fourierInvBCF_one
#print axioms FourierInvFDeriv.spatFDeriv_smul
#print axioms FourierInvFDeriv.isBoundedLinearMap_spatFDeriv
#print axioms FourierInvFDeriv.norm_spatFDeriv_sub_op
#print axioms FourierInvFDeriv.hasFDerivAt_evMap
#print axioms FourierInvFDeriv.fderiv_evMap
#print axioms FourierInvFDeriv.differentiable_evMap
#print axioms FourierInvFDeriv.norm_evFDeriv_sub_le
#print axioms FourierInvFDeriv.continuous_evFDeriv
#print axioms FourierInvFDeriv.contDiff_one_evMap

end FourierInvFDeriv
