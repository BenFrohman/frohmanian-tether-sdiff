import Mathlib.Analysis.Distribution.FourierMultiplier
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! # Fourier-side `H² ↪ L^∞` on ℝ³ for Schwartz functions

`‖g x‖ ≤ (∫ (1 + 4π²|ξ|²)^{-2} dξ)^{1/2} ‖g - Δg‖_{L²}` (Fourier inversion, Plancherel,
Cauchy–Schwarz). -/

open MeasureTheory SchwartzMap FourierTransform Real
open scoped ENNReal Laplacian

noncomputable section
namespace FourierEmb

abbrev E3 := EuclideanSpace ℝ (Fin 3)


/-- Fourier weight `w ξ = 1 + (2π)² ‖ξ‖²`. -/
def w (ξ : E3) : ℝ := 1 + (2 * π) ^ 2 * ‖ξ‖ ^ 2

lemma w_pos (ξ : E3) : 0 < w ξ := by unfold w; positivity

/-- Pointwise bound by the `L¹` norm of the Fourier transform. -/
lemma enorm_le_lintegral_fourier (g : 𝓢(E3, ℂ)) (x : E3) :
    ‖g x‖ₑ ≤ ∫⁻ ξ, ‖𝓕 g ξ‖ₑ := by
  have h1 : g x = 𝓕⁻ (𝓕 g) x := by rw [fourierInv_fourier_eq]
  rw [h1, fourierInv_coe, Real.fourierInv_eq]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  refine lintegral_congr fun ξ => ?_
  rw [Circle.smul_def, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, norm_smul,
    Circle.norm_coe, one_mul]

set_option backward.isDefEq.respectTransparency false in
/-- `𝓕(g - Δg) = w · 𝓕 g`. -/
lemma fourier_sub_laplacian (g : 𝓢(E3, ℂ)) (ξ : E3) :
    𝓕 (g - Δ g) ξ = (w ξ : ℂ) * 𝓕 g ξ := by
  have hT : (fun x : E3 => ‖x‖ ^ 2).HasTemperateGrowth := by fun_prop
  rw [laplacian_eq_fourierMultiplierCLM, fourierMultiplierCLM_apply, sub_eq_add_neg,
    FourierAdd.fourier_add, FourierTransform.fourier_neg, fourier_smul, fourier_fourierInv_eq]
  rw [SchwartzMap.add_apply, SchwartzMap.neg_apply, SchwartzMap.smul_apply,
    smulLeftCLM_apply_apply hT]
  simp only [w, Complex.real_smul]
  push_cast
  ring

/-- `|ξ|`-weight integrability on ℝ³: `∫ w⁻² < ∞`. -/
lemma lintegral_w_inv_sq_lt_top : ∫⁻ ξ : E3, ENNReal.ofReal (w ξ)⁻¹ ^ (2 : ℝ) < ⊤ := by
  have hint : Integrable (fun ξ : E3 => 4 * (1 + ‖ξ‖) ^ (-(4 : ℝ))) :=
    (integrable_one_add_norm (by simp; norm_num)).const_mul _
  refine lt_of_le_of_lt (lintegral_mono fun ξ => ?_) hint.lintegral_lt_top
  have hw := w_pos ξ
  have hn : 0 < 1 + ‖ξ‖ := by positivity
  have hpi : (1 : ℝ) ≤ (2 * π) ^ 2 := by nlinarith [Real.two_le_pi]
  have h1 : (1 + ‖ξ‖) ^ 2 ≤ 2 * w ξ := by
    unfold w; nlinarith [norm_nonneg ξ, sq_nonneg (‖ξ‖ - 1), mul_le_mul_of_nonneg_right hpi
      (sq_nonneg ‖ξ‖)]
  have h2 : (1 + ‖ξ‖) ^ 4 / 4 ≤ w ξ ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) h1 2
    nlinarith
  have h3 : (w ξ)⁻¹ ^ 2 ≤ 4 * (1 + ‖ξ‖) ^ (-(4 : ℝ)) := by
    rw [Real.rpow_neg hn.le, show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      inv_pow]
    have := inv_anti₀ (by positivity) h2
    calc (w ξ ^ 2)⁻¹ ≤ ((1 + ‖ξ‖) ^ 4 / 4)⁻¹ := this
      _ = _ := by push_cast; field_simp
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact h3

lemma enorm_rpow_two (z : ℂ) : ‖z‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
  norm_cast

/-- Plancherel in `lintegral` form. -/
lemma lintegral_fourier_sq (f : 𝓢(E3, ℂ)) :
    ∫⁻ ξ, ‖𝓕 f ξ‖ₑ ^ (2 : ℝ) = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) := by
  have hi : ∀ g : 𝓢(E3, ℂ), Integrable (fun x => ‖g x‖ ^ 2) := fun g =>
    (g.memLp (2 : ℕ)).integrable_norm_pow two_ne_zero
  simp only [enorm_rpow_two]
  rw [← ofReal_integral_eq_lintegral_ofReal (hi _) (Filter.Eventually.of_forall fun _ => by
    positivity), ← ofReal_integral_eq_lintegral_ofReal (hi _)
    (Filter.Eventually.of_forall fun _ => by positivity), integral_norm_sq_fourier]

/-- **Fourier-side `H² ↪ L^∞` on ℝ³ (Schwartz class).** -/
theorem enorm_le_weight_L2 (g : 𝓢(E3, ℂ)) (x : E3) :
    ‖g x‖ₑ ≤ (∫⁻ ξ : E3, ENNReal.ofReal (w ξ)⁻¹ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
      (∫⁻ y, ‖(g - Δ g) y‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  have hpt : ∀ ξ, ‖𝓕 g ξ‖ₑ = ENNReal.ofReal (w ξ)⁻¹ * ‖𝓕 (g - Δ g) ξ‖ₑ := by
    intro ξ
    rw [fourier_sub_laplacian, enorm_mul, ← ofReal_norm_eq_enorm (w ξ : ℂ), Complex.norm_real,
      Real.norm_of_nonneg (w_pos ξ).le, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2
      (w_pos ξ).le), inv_mul_cancel₀ (w_pos ξ).ne', ENNReal.ofReal_one, one_mul]
  have hm1 : AEMeasurable (fun ξ : E3 => ENNReal.ofReal (w ξ)⁻¹) := by
    have : Continuous w := by unfold w; fun_prop
    exact (ENNReal.measurable_ofReal.comp (this.inv₀ fun ξ => (w_pos ξ).ne').measurable).aemeasurable
  have hm2 : AEMeasurable (fun ξ => ‖𝓕 (g - Δ g) ξ‖ₑ) :=
    (𝓕 (g - Δ g)).continuous.enorm.measurable.aemeasurable
  calc ‖g x‖ₑ ≤ ∫⁻ ξ, ‖𝓕 g ξ‖ₑ := enorm_le_lintegral_fourier g x
    _ = ∫⁻ ξ, ((fun ξ => ENNReal.ofReal (w ξ)⁻¹) * fun ξ => ‖𝓕 (g - Δ g) ξ‖ₑ) ξ :=
        lintegral_congr fun ξ => hpt ξ
    _ ≤ _ := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two hm1 hm2
    _ = _ := by rw [lintegral_fourier_sq]

end FourierEmb

#print axioms FourierEmb.enorm_le_weight_L2
#print axioms FourierEmb.lintegral_w_inv_sq_lt_top
