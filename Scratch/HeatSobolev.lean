import Scratch.SobolevFourier

/-! # Heat semigroup on the Fourier-side Sobolev scale (item 2: smoothing)

* `fourierEnergy_heat_le`: `‖e^{τΔ}F‖²_{H^m} ≤ ‖F‖²_{H^m}`;
* `fourierEnergy_heat_succ_le`: `‖e^{τΔ}F‖²_{H^{m+1}} ≤ (1 + 1/(2τ)) ‖F‖²_{H^m}` (`τ > 0`). -/

open MeasureTheory FourierTransform Real
open scoped ENNReal

noncomputable section
namespace HeatSobolev

open LerayHeat SobolevFourier

/-- Real Sobolev polynomial `S_m(a) = ∑_{k ≤ m} a^k`. -/
def Sp (m : ℕ) (a : ℝ) : ℝ := ∑ k ∈ Finset.range (m + 1), a ^ k

lemma Sp_nonneg (m : ℕ) {a : ℝ} (ha : 0 ≤ a) : 0 ≤ Sp m a :=
  Finset.sum_nonneg fun k _ => pow_nonneg ha k

lemma sobW_eq_Sp (m : ℕ) (ξ : E3) : sobW m ξ = ENNReal.ofReal (Sp m (4 * π ^ 2 * ‖ξ‖ ^ 2)) :=
  sobW_eq m ξ

lemma Sp_succ_le (m : ℕ) {a : ℝ} (ha : 0 ≤ a) : Sp (m + 1) a ≤ (1 + a) * Sp m a := by
  have h1 : a ^ m ≤ ∑ k ∈ Finset.range (m + 1), a ^ k :=
    Finset.single_le_sum (f := fun k => a ^ k) (fun k _ => pow_nonneg ha k)
      (Finset.self_mem_range_succ m)
  unfold Sp
  rw [Finset.sum_range_succ _ (m + 1), add_mul, one_mul, pow_succ]
  nlinarith

lemma mul_exp_neg_le {a τ : ℝ} (ha : 0 ≤ a) (hτ : 0 < τ) :
    a * Real.exp (-(2 * τ * a)) ≤ 1 / (2 * τ) := by
  have h := Real.add_one_le_exp (2 * τ * a)
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  nlinarith

lemma gauss_sq {τ : ℝ} (hτ : 0 ≤ τ) (ξ : E3) :
    gauss τ ξ ^ 2 = Real.exp (-(2 * τ * (4 * π ^ 2 * ‖ξ‖ ^ 2))) := by
  rw [gauss, max_eq_left hτ, ← Real.exp_nat_mul]; congr 1; push_cast; ring

/-- Pointwise smoothing inequality `S_{m+1}(a) e^{-2τa} ≤ (1 + 1/(2τ)) S_m(a)`. -/
lemma Sp_succ_gauss_le (m : ℕ) {τ : ℝ} (hτ : 0 < τ) (ξ : E3) :
    Sp (m + 1) (4 * π ^ 2 * ‖ξ‖ ^ 2) * gauss τ ξ ^ 2 ≤
      (1 + 1 / (2 * τ)) * Sp m (4 * π ^ 2 * ‖ξ‖ ^ 2) := by
  set a := 4 * π ^ 2 * ‖ξ‖ ^ 2
  have ha : 0 ≤ a := by positivity
  rw [gauss_sq hτ.le]
  have hS := Sp_succ_le m ha
  have hS0 := Sp_nonneg m ha
  have he := Real.exp_pos (-(2 * τ * a))
  have he1 : Real.exp (-(2 * τ * a)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  have hm := mul_exp_neg_le ha hτ
  calc Sp (m + 1) a * Real.exp (-(2 * τ * a))
      ≤ (1 + a) * Sp m a * Real.exp (-(2 * τ * a)) := mul_le_mul_of_nonneg_right hS he.le
    _ = Sp m a * (Real.exp (-(2 * τ * a)) + a * Real.exp (-(2 * τ * a))) := by ring
    _ ≤ Sp m a * (1 + 1 / (2 * τ)) := mul_le_mul_of_nonneg_left (add_le_add he1 hm) hS0
    _ = _ := by ring

lemma enorm_heat_fourier (τ : ℝ) (F : L2V) :
    ∀ᵐ ξ, ‖((𝓕 (heat τ F) : L2V) : E3 → V) ξ‖ₑ ^ 2 =
      ENNReal.ofReal (gauss τ ξ ^ 2) * ‖((𝓕 F : L2V) : E3 → V) ξ‖ₑ ^ 2 := by
  filter_upwards [coeFn_fourier_heat τ F] with ξ h
  rw [h, enorm_smul, mul_pow, ← ofReal_norm_eq_enorm, Complex.norm_real,
    Real.norm_of_nonneg (gauss_pos τ ξ).le, ENNReal.ofReal_pow (gauss_pos τ ξ).le]

/-- `e^{τΔ}` is a contraction on every Fourier `H^m`. -/
theorem fourierEnergy_heat_le (m : ℕ) (τ : ℝ) (F : L2V) :
    fourierEnergy m (heat τ F) ≤ fourierEnergy m F := by
  unfold fourierEnergy
  refine lintegral_mono_ae ?_
  filter_upwards [enorm_heat_fourier τ F] with ξ h
  rw [h, ← mul_assoc]
  refine mul_le_mul_left ?_ _
  calc sobW m ξ * ENNReal.ofReal (gauss τ ξ ^ 2) ≤ sobW m ξ * 1 := by
        refine mul_le_mul_right ?_ _
        rw [ENNReal.ofReal_le_one]
        exact pow_le_one₀ (gauss_pos τ ξ).le (gauss_le_one τ ξ)
    _ = sobW m ξ := mul_one _

/-- **Parabolic smoothing**: `‖e^{τΔ}F‖²_{H^{m+1}} ≤ (1 + 1/(2τ)) ‖F‖²_{H^m}` for `τ > 0`. -/
theorem fourierEnergy_heat_succ_le (m : ℕ) {τ : ℝ} (hτ : 0 < τ) (F : L2V) :
    fourierEnergy (m + 1) (heat τ F) ≤ ENNReal.ofReal (1 + 1 / (2 * τ)) * fourierEnergy m F := by
  unfold fourierEnergy
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [enorm_heat_fourier τ F] with ξ h
  rw [h, ← mul_assoc, ← mul_assoc]
  refine mul_le_mul_left ?_ _
  rw [sobW_eq_Sp, sobW_eq_Sp, ← ENNReal.ofReal_mul (Sp_nonneg _ (by positivity)),
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (Sp_succ_gauss_le m hτ ξ)

end HeatSobolev

#print axioms HeatSobolev.fourierEnergy_heat_le
#print axioms HeatSobolev.fourierEnergy_heat_succ_le
