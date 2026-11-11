import Scratch.ProductEstimate
import Scratch.SobolevHilbert
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-! # Inverse Fourier of `Ĥ^m`: moment integrability and `C^n` regularity

Converse to the Fourier–Sobolev matching: if `G ∈ Ĥ^m` and `m ≥ n + 2`, then
`ξ ↦ ‖ξ‖^n ‖G ξ‖` is integrable, so `𝓕⁻ G` is `C^n`. If a physical `L²` field has
finite Fourier energy of every order, `𝓕⁻ (𝓕 F)` is `C^∞`. -/

open MeasureTheory FourierTransform Real
open scoped ENNReal

set_option autoImplicit false

noncomputable section
namespace InverseSobolev

open LerayHeat SobolevFourier SobolevHilbert
open ProductEstimate (Cw Cw_lt_top one_le_ω)

/-- Local name for the Japanese-bracket weight `ω(ξ) = 1 + 4π²|ξ|²` as `ℝ≥0∞`. -/
abbrev ω := ProductEstimate.ω

/-! ## Comparison of `sobW m` with `ω^m` -/

lemma one_le_w (ξ : E3) : 1 ≤ FourierEmb.w ξ := by
  unfold FourierEmb.w; nlinarith [sq_nonneg ‖ξ‖, pi_pos]

lemma sum_geom_le (a : ℝ) (ha : 0 ≤ a) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), a ^ k ≤ (m + 1) * (1 + a) ^ m := by
  have h1 : 1 ≤ 1 + a := le_add_of_nonneg_right ha
  have hterm : ∀ k ∈ Finset.range (m + 1), a ^ k ≤ (1 + a) ^ m := fun k hk =>
    (pow_le_pow_left₀ ha (le_add_of_nonneg_left zero_le_one) k).trans
      (pow_le_pow_right₀ h1 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)))
  refine (Finset.sum_le_sum hterm).trans ?_
  simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

lemma one_add_pow_le_two_pow_sum (a : ℝ) (ha : 0 ≤ a) (m : ℕ) :
    (1 + a) ^ m ≤ (2 : ℝ) ^ m * ∑ k ∈ Finset.range (m + 1), a ^ k := by
  rw [add_comm, add_pow]
  have hC : ∀ k ∈ Finset.range (m + 1), (m.choose k : ℝ) ≤ (2 : ℝ) ^ m := fun k _ => by
    have hch : (m.choose k : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := Nat.cast_le.2 (Nat.choose_le_two_pow m k)
    have he : ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ m := Nat.cast_pow (2 : ℕ) m
    rwa [he] at hch
  have hterm : ∀ k ∈ Finset.range (m + 1),
      a ^ k * 1 ^ (m - k) * (m.choose k : ℝ) ≤ (2 : ℝ) ^ m * a ^ k := fun k hk => by
    simp only [one_pow, mul_one]
    have : (m.choose k : ℝ) * a ^ k ≤ (2 : ℝ) ^ m * a ^ k :=
      mul_le_mul_of_nonneg_right (hC k hk) (pow_nonneg ha _)
    rw [mul_comm (a ^ k)]; exact this
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]

lemma sobW_le_mul_ω_pow (m : ℕ) (ξ : E3) :
    sobW m ξ ≤ ENNReal.ofReal (m + 1 : ℝ) * ω ξ ^ m := by
  have ha : 0 ≤ 4 * π ^ 2 * ‖ξ‖ ^ 2 := by positivity
  have hw : FourierEmb.w ξ = 1 + 4 * π ^ 2 * ‖ξ‖ ^ 2 := by unfold FourierEmb.w; ring
  have hw0 : 0 ≤ 1 + 4 * π ^ 2 * ‖ξ‖ ^ 2 := add_nonneg zero_le_one ha
  rw [sobW_eq, ω, ProductEstimate.ω, hw, ← ENNReal.ofReal_pow hw0,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (m + 1 : ℝ))]
  exact ENNReal.ofReal_le_ofReal (sum_geom_le _ ha m)

lemma ω_pow_le_mul_sobW (m : ℕ) (ξ : E3) :
    ω ξ ^ m ≤ ENNReal.ofReal ((2 : ℝ) ^ m) * sobW m ξ := by
  have ha : 0 ≤ 4 * π ^ 2 * ‖ξ‖ ^ 2 := by positivity
  have hw : FourierEmb.w ξ = 1 + 4 * π ^ 2 * ‖ξ‖ ^ 2 := by unfold FourierEmb.w; ring
  have hw0 : 0 ≤ 1 + 4 * π ^ 2 * ‖ξ‖ ^ 2 := add_nonneg zero_le_one ha
  rw [sobW_eq, ω, ProductEstimate.ω, hw, ← ENNReal.ofReal_pow hw0,
    ← ENNReal.ofReal_mul (pow_nonneg (by norm_num) m)]
  exact ENNReal.ofReal_le_ofReal (one_add_pow_le_two_pow_sum _ ha m)

lemma ω_pow_ne_zero (m : ℕ) (ξ : E3) : ω ξ ^ m ≠ 0 :=
  (ENNReal.pow_pos (lt_of_lt_of_le zero_lt_one (one_le_ω ξ)) m).ne'

lemma ω_pow_ne_top (m : ℕ) (ξ : E3) : ω ξ ^ m ≠ ⊤ := by
  unfold ω ProductEstimate.ω
  exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top

lemma ω_pow_eq_ofReal (m : ℕ) (ξ : E3) :
    ω ξ ^ m = ENNReal.ofReal (FourierEmb.w ξ ^ m) := by
  unfold ω ProductEstimate.ω
  exact (ENNReal.ofReal_pow (FourierEmb.w_pos ξ).le m).symm

lemma xi_pow_div_w {n m : ℕ} (hm : n + 2 ≤ m) (ξ : E3) :
    ‖ξ‖ ^ (2 * n) / FourierEmb.w ξ ^ m ≤
      (4 * π ^ 2)⁻¹ ^ n * (FourierEmb.w ξ)⁻¹ ^ 2 := by
  have hw : 0 < FourierEmb.w ξ := FourierEmb.w_pos ξ
  have h1w : 1 ≤ FourierEmb.w ξ := one_le_w ξ
  have ha : 0 ≤ 4 * π ^ 2 * ‖ξ‖ ^ 2 := by positivity
  have hπ : 0 < 4 * π ^ 2 := by positivity
  have hden : FourierEmb.w ξ ^ (n + 2) ≤ FourierEmb.w ξ ^ m := pow_le_pow_right₀ h1w hm
  have hwform : FourierEmb.w ξ = 1 + 4 * π ^ 2 * ‖ξ‖ ^ 2 := by unfold FourierEmb.w; ring
  have hnum : ‖ξ‖ ^ (2 * n) = (4 * π ^ 2)⁻¹ ^ n * (4 * π ^ 2 * ‖ξ‖ ^ 2) ^ n := by
    rw [pow_mul ‖ξ‖ 2 n, mul_pow, ← mul_assoc, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero n hπ.ne'), one_mul]
  have hleξ : 4 * π ^ 2 * ‖ξ‖ ^ 2 ≤ FourierEmb.w ξ := by
    rw [hwform]; exact le_add_of_nonneg_left zero_le_one
  have hfrac : (4 * π ^ 2 * ‖ξ‖ ^ 2) ^ n / FourierEmb.w ξ ^ (n + 2) ≤
      (FourierEmb.w ξ)⁻¹ ^ 2 := by
    have : (4 * π ^ 2 * ‖ξ‖ ^ 2) ^ n / FourierEmb.w ξ ^ (n + 2) ≤
        FourierEmb.w ξ ^ n / FourierEmb.w ξ ^ (n + 2) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ ha hleξ n) (pow_nonneg hw.le _)
    refine this.trans (le_of_eq ?_)
    rw [pow_add, div_mul_eq_div_div, pow_two, div_self (pow_pos hw n).ne', one_div, inv_pow]
    ring
  have hmain : ‖ξ‖ ^ (2 * n) / FourierEmb.w ξ ^ (n + 2) ≤
      (4 * π ^ 2)⁻¹ ^ n * (FourierEmb.w ξ)⁻¹ ^ 2 := by
    calc ‖ξ‖ ^ (2 * n) / FourierEmb.w ξ ^ (n + 2)
        = ((4 * π ^ 2)⁻¹ ^ n * (4 * π ^ 2 * ‖ξ‖ ^ 2) ^ n) / FourierEmb.w ξ ^ (n + 2) := by
          rw [hnum]
      _ = (4 * π ^ 2)⁻¹ ^ n * ((4 * π ^ 2 * ‖ξ‖ ^ 2) ^ n / FourierEmb.w ξ ^ (n + 2)) := by
          ring
      _ ≤ (4 * π ^ 2)⁻¹ ^ n * (FourierEmb.w ξ)⁻¹ ^ 2 :=
          mul_le_mul_of_nonneg_left hfrac (pow_nonneg (inv_nonneg.2 hπ.le) n)
  exact (div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg _) _) (pow_pos hw _) hden).trans hmain

lemma lintegral_xi_pow_div_w {n m : ℕ} (hm : n + 2 ≤ m) :
    ∫⁻ ξ : E3, ENNReal.ofReal (‖ξ‖ ^ (2 * n) / FourierEmb.w ξ ^ m) < ⊤ := by
  have hnn : 0 ≤ (4 * π ^ 2)⁻¹ ^ n := pow_nonneg (inv_nonneg.2 (by positivity)) n
  have hle : ∀ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * n) / FourierEmb.w ξ ^ m) ≤
      ENNReal.ofReal ((4 * π ^ 2)⁻¹ ^ n) * ENNReal.ofReal ((FourierEmb.w ξ)⁻¹ ^ 2) := fun ξ => by
    rw [← ENNReal.ofReal_mul hnn]
    exact ENNReal.ofReal_le_ofReal (xi_pow_div_w hm ξ)
  refine (lintegral_mono hle).trans_lt ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hCw : ∫⁻ ξ, ENNReal.ofReal ((FourierEmb.w ξ)⁻¹ ^ 2) = Cw := by
    unfold Cw
    refine lintegral_congr fun ξ => ?_
    have ha : 0 ≤ (FourierEmb.w ξ)⁻¹ := inv_nonneg.2 (FourierEmb.w_pos ξ).le
    rw [ENNReal.ofReal_pow ha, ProductEstimate.rpow_two']
  rw [hCw]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top Cw_lt_top

#print axioms InverseSobolev.sobW_le_mul_ω_pow
#print axioms InverseSobolev.ω_pow_le_mul_sobW
#print axioms InverseSobolev.xi_pow_div_w
#print axioms InverseSobolev.lintegral_xi_pow_div_w

end InverseSobolev
