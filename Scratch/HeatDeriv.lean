import Scratch.Duhamel
import Scratch.ProductHm
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Complex.Module

/-! # Time derivative of the heat semigroup on `Ĥ^s`

The Fourier-side Laplacian `lapH : Ĥ^{m+2} →L Ĥ^m` is multiplication by
`-4π²|ξ|²`. For `G ∈ Ĥ^{m+2}` and `τ ≥ 0`, the curve
`σ ↦ e^{σΔ} G`, viewed in `Ĥ^m`, has a one-sided derivative at `τ` along
`[0, ∞)` equal to `e^{τΔ}(Δ G)`. -/

open MeasureTheory FourierTransform Real Filter Topology Set
open scoped ENNReal

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
namespace HeatDeriv

open LerayHeat SobolevFourier SobolevHilbert Duhamel ProductHm

/-! ## The Laplacian multiplier `Ĥ^{m+2} → Ĥ^m` -/

/-- Fourier symbol of `Δ`: multiplication by `-4π²|ξ|²`. -/
def lapSym (ξ : E3) : V →L[ℂ] V :=
  ((-(4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ)) • ContinuousLinearMap.id ℂ V

lemma lapSym_apply (ξ : E3) (v : V) :
    lapSym ξ v = ((-(4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ)) • v := rfl

lemma lapSym_meas (g : E3 → V) (hg : AEStronglyMeasurable g) :
    AEStronglyMeasurable (fun ξ => lapSym ξ (g ξ)) := by
  simp only [lapSym_apply]
  have hc : Continuous fun ξ : E3 => ((-(4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ)) := by
    fun_prop
  exact hc.aestronglyMeasurable.smul hg

lemma norm_lapSym (ξ : E3) : ‖lapSym ξ‖ ≤ 4 * π ^ 2 * ‖ξ‖ ^ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [lapSym_apply, norm_smul]
  have hre : ‖((- (4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ))‖ = 4 * π ^ 2 * ‖ξ‖ ^ 2 := by
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hre]

lemma enorm_lapSym_sq (ξ : E3) :
    ‖lapSym ξ‖ₑ ^ 2 ≤ ENNReal.ofReal ((4 * π ^ 2 * ‖ξ‖ ^ 2) ^ 2) := by
  have h := norm_lapSym ξ
  have hnn : 0 ≤ 4 * π ^ 2 * ‖ξ‖ ^ 2 := by positivity
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) h 2)

/-- `sobW m · (4π²|ξ|²)² ≤ sobW (m+2)`. -/
lemma sobW_mul_xi4 (m : ℕ) (ξ : E3) :
    sobW m ξ * ENNReal.ofReal ((4 * π ^ 2 * ‖ξ‖ ^ 2) ^ 2) ≤ sobW (m + 2) ξ := by
  have ha : 0 ≤ 4 * π ^ 2 * ‖ξ‖ ^ 2 := by positivity
  have hsum : 0 ≤ ∑ k ∈ Finset.range (m + 1), (4 * π ^ 2 * ‖ξ‖ ^ 2) ^ k :=
    Finset.sum_nonneg fun _ _ => pow_nonneg ha _
  rw [sobW_eq, sobW_eq, ← ENNReal.ofReal_mul hsum]
  refine ENNReal.ofReal_le_ofReal ?_
  have hre : (∑ k ∈ Finset.range (m + 1), (4 * π ^ 2 * ‖ξ‖ ^ 2) ^ k) *
      (4 * π ^ 2 * ‖ξ‖ ^ 2) ^ 2 =
      ∑ k ∈ Finset.range (m + 1), (4 * π ^ 2 * ‖ξ‖ ^ 2) ^ (k + 2) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_add]
  rw [hre]
  have hpeel :
      ∑ j ∈ Finset.range (m + 3), (4 * π ^ 2 * ‖ξ‖ ^ 2) ^ j =
        1 + (4 * π ^ 2 * ‖ξ‖ ^ 2) +
          ∑ k ∈ Finset.range (m + 1), (4 * π ^ 2 * ‖ξ‖ ^ 2) ^ (k + 2) := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp [pow_zero, pow_one]
    abel
  have hrest :
      0 ≤ 1 + (4 * π ^ 2 * ‖ξ‖ ^ 2) := add_nonneg zero_le_one ha
  have : ∑ k ∈ Finset.range (m + 1), (4 * π ^ 2 * ‖ξ‖ ^ 2) ^ (k + 2) ≤
      ∑ j ∈ Finset.range (m + 3), (4 * π ^ 2 * ‖ξ‖ ^ 2) ^ j := by
    linarith [hpeel, hrest, Finset.sum_nonneg (s := Finset.range (m + 1))
      (fun k _ => pow_nonneg ha (k + 2))]
  exact this

lemma bound_lap (m : ℕ) (ξ : E3) :
    sobW m ξ * ‖lapSym ξ‖ₑ ^ 2 ≤ ENNReal.ofReal 1 * sobW (m + 2) ξ := by
  refine (mul_le_mul_of_nonneg_left (enorm_lapSym_sq ξ) (zero_le _)).trans ?_
  rw [ENNReal.ofReal_one, one_mul]
  exact sobW_mul_xi4 m ξ

/-- **Laplacian** `Δ : Ĥ^{m+2} → Ĥ^m`, as a Fourier multiplier. -/
def lapH (m : ℕ) : Hm (m + 2) →L[ℂ] Hm m :=
  wmul lapSym lapSym_meas 1 zero_le_one (bound_lap m)

lemma coeFn_lapH (m : ℕ) (G : Hm (m + 2)) :
    (lapH m G : E3 → V) =ᵐ[μw m] fun ξ =>
      ((-(4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ)) • (G : E3 → V) ξ :=
  (coeFn_wmul lapSym lapSym_meas 1 zero_le_one (bound_lap m) G).trans
    (Eventually.of_forall fun ξ => lapSym_apply ξ _)

lemma incl_le_add_two (m : ℕ) : m ≤ m + 2 := Nat.le_add_right _ _

/-! ## One-sided derivative of the Gaussian symbol on `[0, ∞)` -/

lemma gauss_eq_of_nonneg {σ : ℝ} (hσ : 0 ≤ σ) (ξ : E3) :
    gauss σ ξ = Real.exp (-(4 * π ^ 2 * σ * ‖ξ‖ ^ 2)) := by
  unfold gauss
  rw [max_eq_left hσ]

lemma hasDerivWithinAt_gauss (ξ : E3) {τ : ℝ} (hτ : 0 ≤ τ) :
    HasDerivWithinAt (fun σ => gauss σ ξ)
      (-(4 * π ^ 2 * ‖ξ‖ ^ 2) * gauss τ ξ) (Ici (0 : ℝ)) τ := by
  have hfun :
      EqOn (fun σ => gauss σ ξ)
        (fun σ => Real.exp (-(4 * π ^ 2 * σ * ‖ξ‖ ^ 2))) (Ici (0 : ℝ)) :=
    fun σ hσ => gauss_eq_of_nonneg hσ ξ
  have hlin : HasDerivAt (fun σ : ℝ => -(4 * π ^ 2 * σ * ‖ξ‖ ^ 2))
      (-(4 * π ^ 2 * ‖ξ‖ ^ 2)) τ := by
    have h1 : HasDerivAt (fun σ : ℝ => σ * (4 * π ^ 2 * ‖ξ‖ ^ 2))
        (4 * π ^ 2 * ‖ξ‖ ^ 2) τ := by
      simpa using (hasDerivAt_id τ).mul_const (4 * π ^ 2 * ‖ξ‖ ^ 2)
    have hfun' : (fun σ : ℝ => -(4 * π ^ 2 * σ * ‖ξ‖ ^ 2)) =
        fun σ => -(σ * (4 * π ^ 2 * ‖ξ‖ ^ 2)) := by
      ext σ; ring
    rw [hfun']
    exact h1.neg
  have hder : HasDerivAt (fun σ => Real.exp (-(4 * π ^ 2 * σ * ‖ξ‖ ^ 2)))
      (Real.exp (-(4 * π ^ 2 * τ * ‖ξ‖ ^ 2)) * (-(4 * π ^ 2 * ‖ξ‖ ^ 2))) τ :=
    hlin.exp
  have hder' : HasDerivAt (fun σ => Real.exp (-(4 * π ^ 2 * σ * ‖ξ‖ ^ 2)))
      (-(4 * π ^ 2 * ‖ξ‖ ^ 2) * Real.exp (-(4 * π ^ 2 * τ * ‖ξ‖ ^ 2))) τ := by
    convert hder using 1
    ring
  have : HasDerivWithinAt (fun σ => Real.exp (-(4 * π ^ 2 * σ * ‖ξ‖ ^ 2)))
      (-(4 * π ^ 2 * ‖ξ‖ ^ 2) * Real.exp (-(4 * π ^ 2 * τ * ‖ξ‖ ^ 2)))
      (Ici (0 : ℝ)) τ :=
    hder'.hasDerivWithinAt
  rw [gauss_eq_of_nonneg hτ ξ]
  exact this.congr hfun (hfun hτ)

/-- Bound: `|g(σ) - g(τ)| ≤ (4π²|ξ|²) |σ - τ|` for `σ, τ ≥ 0`. -/
lemma gauss_lip {σ τ : ℝ} (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (ξ : E3) :
    |gauss σ ξ - gauss τ ξ| ≤ (4 * π ^ 2 * ‖ξ‖ ^ 2) * |σ - τ| := by
  rw [gauss_eq_of_nonneg hσ, gauss_eq_of_nonneg hτ]
  set a := 4 * π ^ 2 * ‖ξ‖ ^ 2
  have ha : 0 ≤ a := by positivity
  have haσ : 4 * π ^ 2 * σ * ‖ξ‖ ^ 2 = a * σ := by unfold a; ring
  have haτ : 4 * π ^ 2 * τ * ‖ξ‖ ^ 2 = a * τ := by unfold a; ring
  rw [haσ, haτ]
  wlog hst : τ ≤ σ generalizing σ τ
  · rw [abs_sub_comm, abs_sub_comm σ]
    exact this hτ hσ (by unfold a; ring) (by unfold a; ring) (le_of_not_ge hst)
  have ht : 0 ≤ σ - τ := sub_nonneg.2 hst
  have hexp_le : Real.exp (-(a * σ)) ≤ Real.exp (-(a * τ)) :=
    Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hst ha))
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hexp_le), abs_of_nonneg ht]
  have hfac :
      Real.exp (-(a * σ)) = Real.exp (-(a * τ)) * Real.exp (-(a * (σ - τ))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hre :
      Real.exp (-(a * τ)) - Real.exp (-(a * σ)) =
        Real.exp (-(a * τ)) * (1 - Real.exp (-(a * (σ - τ)))) := by
    rw [hfac]; ring
  have hexp1 : Real.exp (-(a * τ)) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg ha hτ))
  have hpos : 0 ≤ 1 - Real.exp (-(a * (σ - τ))) :=
    sub_nonneg.2 (Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg ha ht)))
  have hmain : Real.exp (-(a * τ)) - Real.exp (-(a * σ)) ≤
      1 - Real.exp (-(a * (σ - τ))) := by
    rw [hre]
    exact mul_le_of_le_one_left hpos hexp1
  have hx : 0 ≤ a * (σ - τ) := mul_nonneg ha ht
  have hineq : 1 - Real.exp (-(a * (σ - τ))) ≤ a * (σ - τ) := by
    have := Real.add_one_le_exp (-(a * (σ - τ)))
    linarith
  exact hmain.trans hineq

lemma gauss_remainder_bound {σ τ : ℝ} (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (ξ : E3) :
    |gauss σ ξ - gauss τ ξ - (σ - τ) * (-(4 * π ^ 2 * ‖ξ‖ ^ 2) * gauss τ ξ)| ≤
      2 * (4 * π ^ 2 * ‖ξ‖ ^ 2) * |σ - τ| := by
  have ha : 0 ≤ 4 * π ^ 2 * ‖ξ‖ ^ 2 := by positivity
  have hg : 0 ≤ gauss τ ξ := (gauss_pos τ ξ).le
  have h1 := gauss_lip hσ hτ ξ
  have h2 :
      |(σ - τ) * (-(4 * π ^ 2 * ‖ξ‖ ^ 2) * gauss τ ξ)| ≤
        (4 * π ^ 2 * ‖ξ‖ ^ 2) * |σ - τ| := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg ha, abs_of_nonneg hg]
    calc |σ - τ| * ((4 * π ^ 2 * ‖ξ‖ ^ 2) * gauss τ ξ)
        = (4 * π ^ 2 * ‖ξ‖ ^ 2) * gauss τ ξ * |σ - τ| := by ring
      _ ≤ (4 * π ^ 2 * ‖ξ‖ ^ 2) * 1 * |σ - τ| :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (gauss_le_one τ ξ) ha) (abs_nonneg _)
      _ = (4 * π ^ 2 * ‖ξ‖ ^ 2) * |σ - τ| := by ring
  have hadd :=
    abs_add_le (gauss σ ξ - gauss τ ξ)
      (-((σ - τ) * (-(4 * π ^ 2 * ‖ξ‖ ^ 2) * gauss τ ξ)))
  have hre :
      gauss σ ξ - gauss τ ξ - (σ - τ) * (-(4 * π ^ 2 * ‖ξ‖ ^ 2) * gauss τ ξ) =
        (gauss σ ξ - gauss τ ξ) +
          -((σ - τ) * (-(4 * π ^ 2 * ‖ξ‖ ^ 2) * gauss τ ξ)) := by
    ring
  rw [hre]
  refine hadd.trans ?_
  rw [abs_neg]
  linarith [h1, h2]

/-! ## The heat curve in the weaker space `Ĥ^m` -/

/-- `e^{σΔ} G` as an element of `Ĥ^m`, for `G ∈ Ĥ^{m+2}`. -/
def heatOfHigh (m : ℕ) (G : Hm (m + 2)) (σ : ℝ) : Hm m :=
  heatH m σ (incl (incl_le_add_two m) G)

lemma coeFn_heatOfHigh (m : ℕ) (G : Hm (m + 2)) (σ : ℝ) :
    (heatOfHigh m G σ : E3 → V) =ᵐ[μw m] fun ξ =>
      ((gauss σ ξ : ℝ) : ℂ) • (G : E3 → V) ξ := by
  have h1 := coeFn_heatH σ (incl (incl_le_add_two m) G)
  have h2 := coeFn_incl (incl_le_add_two m) G
  refine h1.trans ?_
  filter_upwards [h2] with ξ hξ
  rw [hξ]

lemma coeFn_heat_lapH (m : ℕ) (τ : ℝ) (G : Hm (m + 2)) :
    (heatH m τ (lapH m G) : E3 → V) =ᵐ[μw m] fun ξ =>
      ((gauss τ ξ : ℝ) : ℂ) •
        ((-(4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ)) • (G : E3 → V) ξ := by
  have h1 := coeFn_heatH τ (lapH m G)
  have h2 := coeFn_lapH m G
  refine h1.trans ?_
  filter_upwards [h2] with ξ hξ
  rw [hξ]

/-- Complex form of the first-order remainder of `gauss`. -/
lemma rem_scalar_ofReal (ξ : E3) (σ τ : ℝ) :
    (gauss σ ξ : ℂ) - (gauss τ ξ : ℂ)
      - (σ - τ : ℂ) * (gauss τ ξ : ℂ) * ((-(4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ))
    = ((gauss σ ξ - gauss τ ξ
        - (σ - τ) * (-(4 * π ^ 2 * ‖ξ‖ ^ 2) * gauss τ ξ) : ℝ) : ℂ) := by
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_neg]
  ring

lemma rem_div_le {σ τ : ℝ} (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (ξ : E3) :
    ‖σ - τ‖⁻¹ *
        |gauss σ ξ - gauss τ ξ
          - (σ - τ) * (-(4 * π ^ 2 * ‖ξ‖ ^ 2) * gauss τ ξ)|
      ≤ 2 * (4 * π ^ 2 * ‖ξ‖ ^ 2) := by
  rcases eq_or_ne σ τ with h | h
  · simp [h]
    positivity
  · set rem :=
      gauss σ ξ - gauss τ ξ
        - (σ - τ) * (-(4 * π ^ 2 * ‖ξ‖ ^ 2) * gauss τ ξ)
    set a := 4 * π ^ 2 * ‖ξ‖ ^ 2
    have hb : |rem| ≤ 2 * a * |σ - τ| := gauss_remainder_bound hσ hτ ξ
    have hpos : |σ - τ| ≠ 0 := abs_ne_zero.2 (sub_ne_zero.2 h)
    have hmul : ‖σ - τ‖⁻¹ * |rem| ≤ |σ - τ|⁻¹ * (2 * a * |σ - τ|) := by
      rw [Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hb (inv_nonneg.2 (abs_nonneg _))
    have hsimp : |σ - τ|⁻¹ * (2 * a * |σ - τ|) = 2 * a := by
      rw [mul_comm (2 * a), ← mul_assoc, inv_mul_cancel₀ hpos, one_mul]
    rw [Real.norm_eq_abs]
    exact hmul.trans hsimp.le

lemma coeFn_real_smul_Hm (m : ℕ) (r : ℝ) (F : Hm m) :
    ⇑(r • F) =ᵐ[μw m] fun ξ => (r : ℂ) • (F : E3 → V) ξ := by
  -- `Module ℝ (Hm m)` is `NormedSpace.complexToReal`, so `r • F` is `(r : ℂ) • F`.
  change ⇑((r : ℂ) • F) =ᵐ[μw m] fun ξ => (r : ℂ) • (F : E3 → V) ξ
  exact Lp.coeFn_smul (r : ℂ) F

lemma coeFn_heat_remainder (m : ℕ) (G : Hm (m + 2)) (σ τ : ℝ) :
    ⇑(heatOfHigh m G σ - heatOfHigh m G τ - (σ - τ) • heatH m τ (lapH m G))
      =ᵐ[μw m] fun ξ =>
        ((gauss σ ξ - gauss τ ξ
          - (σ - τ) * (-(4 * π ^ 2 * ‖ξ‖ ^ 2) * gauss τ ξ) : ℝ) : ℂ) •
          (G : E3 → V) ξ := by
  filter_upwards [coeFn_heatOfHigh m G σ, coeFn_heatOfHigh m G τ,
    coeFn_real_smul_Hm m (σ - τ) (heatH m τ (lapH m G)),
    coeFn_heat_lapH m τ G,
    Lp.coeFn_sub (heatOfHigh m G σ) (heatOfHigh m G τ),
    Lp.coeFn_sub (heatOfHigh m G σ - heatOfHigh m G τ)
      ((σ - τ) • heatH m τ (lapH m G))] with ξ hσ hτ hs hl h12 h123
  rw [h123, Pi.sub_apply, h12, Pi.sub_apply, hσ, hτ, hs, hl]
  simp [smul_smul, sub_smul, add_smul, Complex.ofReal_sub, Complex.ofReal_mul]
  congr 1
  ring

/-- The domination `ξ ↦ (2 · 4π²|ξ|² ‖G ξ‖)²` is integrable on `μw m`. -/
lemma lintegral_dom_lt_top (m : ℕ) (G : Hm (m + 2)) :
    ∫⁻ ξ, (ENNReal.ofReal (2 * (4 * π ^ 2 * ‖ξ‖ ^ 2)) *
        ‖(G : E3 → V) ξ‖ₑ) ^ ((2 : ENNReal).toReal) ∂(μw m) < ⊤ := by
  have hG :
      ∫⁻ ξ, ‖(G : E3 → V) ξ‖ₑ ^ ((2 : ENNReal).toReal) ∂(μw (m + 2)) < ⊤ :=
    lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
      (Lp.eLpNorm_lt_top G)
  have hmono :
      ∫⁻ ξ, (ENNReal.ofReal (2 * (4 * π ^ 2 * ‖ξ‖ ^ 2)) *
          ‖(G : E3 → V) ξ‖ₑ) ^ ((2 : ENNReal).toReal) ∂(μw m)
        ≤ 4 * ∫⁻ ξ, ‖(G : E3 → V) ξ‖ₑ ^ ((2 : ENNReal).toReal) ∂(μw (m + 2)) := by
    rw [lintegral_μw, lintegral_μw, ← lintegral_const_mul' _ _ (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)]
    refine lintegral_mono fun ξ => ?_
    have ha : 0 ≤ 4 * π ^ 2 * ‖ξ‖ ^ 2 := by positivity
    have hrpow :
        (ENNReal.ofReal (2 * (4 * π ^ 2 * ‖ξ‖ ^ 2)) * ‖(G : E3 → V) ξ‖ₑ) ^
            ((2 : ENNReal).toReal) =
          ENNReal.ofReal ((2 * (4 * π ^ 2 * ‖ξ‖ ^ 2)) ^ (2 : ℝ)) *
            (‖(G : E3 → V) ξ‖ₑ ^ ((2 : ENNReal).toReal)) := by
      have hnn : 0 ≤ 2 * (4 * π ^ 2 * ‖ξ‖ ^ 2) := by positivity
      simp only [ENNReal.toReal_ofNat]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
        ← ENNReal.ofReal_rpow_of_nonneg hnn (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      sobW m ξ * ((ENNReal.ofReal (2 * (4 * π ^ 2 * ‖ξ‖ ^ 2)) *
          ‖(G : E3 → V) ξ‖ₑ) ^ ((2 : ENNReal).toReal))
          = sobW m ξ * (ENNReal.ofReal ((2 * (4 * π ^ 2 * ‖ξ‖ ^ 2)) ^ (2 : ℝ)) *
              (‖(G : E3 → V) ξ‖ₑ ^ ((2 : ENNReal).toReal))) := by
            rw [hrpow]
        _ = (sobW m ξ * ENNReal.ofReal ((2 * (4 * π ^ 2 * ‖ξ‖ ^ 2)) ^ (2 : ℝ))) *
              (‖(G : E3 → V) ξ‖ₑ ^ ((2 : ENNReal).toReal)) := by
            ring
        _ = (sobW m ξ * ENNReal.ofReal (4 * (4 * π ^ 2 * ‖ξ‖ ^ 2) ^ 2)) *
              (‖(G : E3 → V) ξ‖ₑ ^ ((2 : ENNReal).toReal)) := by
            have : ((2 * (4 * π ^ 2 * ‖ξ‖ ^ 2)) ^ (2 : ℝ)) =
                4 * (4 * π ^ 2 * ‖ξ‖ ^ 2) ^ 2 := by
              rw [show (2 : ℝ) = (2 : ℕ) from rfl, Real.rpow_natCast]
              ring
            rw [this]
        _ = (4 * (sobW m ξ * ENNReal.ofReal ((4 * π ^ 2 * ‖ξ‖ ^ 2) ^ 2))) *
              (‖(G : E3 → V) ξ‖ₑ ^ ((2 : ENNReal).toReal)) := by
            rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat]
            ring
        _ ≤ (4 * sobW (m + 2) ξ) *
              (‖(G : E3 → V) ξ‖ₑ ^ ((2 : ENNReal).toReal)) := by
            have hstep :
                4 * (sobW m ξ * ENNReal.ofReal ((4 * π ^ 2 * ‖ξ‖ ^ 2) ^ 2)) ≤
                  4 * sobW (m + 2) ξ :=
              mul_le_mul_of_nonneg_left (sobW_mul_xi4 m ξ) (zero_le _)
            exact mul_le_mul_of_nonneg_right hstep (zero_le _)
        _ = 4 * (sobW (m + 2) ξ * ‖(G : E3 → V) ξ‖ₑ ^ ((2 : ENNReal).toReal)) := by
            ring
  exact lt_of_le_of_lt hmono (ENNReal.mul_lt_top (by norm_num) hG)

lemma continuous_gauss_remainder (σ τ : ℝ) :
    Continuous fun ξ : E3 =>
      gauss σ ξ - gauss τ ξ - (σ - τ) * (-(4 * π ^ 2 * ‖ξ‖ ^ 2) * gauss τ ξ) := by
  have h1 : Continuous fun ξ : E3 => gauss σ ξ - gauss τ ξ :=
    (continuous_gauss σ).sub (continuous_gauss τ)
  have h2 : Continuous fun ξ : E3 =>
      (σ - τ) * (-(4 * π ^ 2 * ‖ξ‖ ^ 2) * gauss τ ξ) := by
    have hξ : Continuous fun ξ : E3 => ‖ξ‖ ^ 2 := continuous_norm.pow 2
    exact continuous_const.mul <| (continuous_const.mul hξ).neg.mul (continuous_gauss τ)
  exact h1.sub h2

lemma enorm_slope_eq (σ τ : ℝ) (ξ : E3) (v : V) :
    ‖(((‖σ - τ‖⁻¹ *
        (gauss σ ξ - gauss τ ξ
          - (σ - τ) * (-(4 * π ^ 2 * ‖ξ‖ ^ 2) * gauss τ ξ)) : ℝ) : ℂ) • v)‖ₑ
      = ENNReal.ofReal (‖σ - τ‖⁻¹ *
          |gauss σ ξ - gauss τ ξ
            - (σ - τ) * (-(4 * π ^ 2 * ‖ξ‖ ^ 2) * gauss τ ξ)|) * ‖v‖ₑ := by
  rw [enorm_smul]
  have hsc :
      ‖(((‖σ - τ‖⁻¹ *
          (gauss σ ξ - gauss τ ξ
            - (σ - τ) * (-(4 * π ^ 2 * ‖ξ‖ ^ 2) * gauss τ ξ)) : ℝ) : ℂ))‖ₑ
        = ENNReal.ofReal (‖σ - τ‖⁻¹ *
            |gauss σ ξ - gauss τ ξ
              - (σ - τ) * (-(4 * π ^ 2 * ‖ξ‖ ^ 2) * gauss τ ξ)|) := by
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (inv_nonneg.2 (norm_nonneg _))]
  rw [hsc]

lemma norm_heat_slope (m : ℕ) (G : Hm (m + 2)) (σ τ : ℝ) :
    ‖σ - τ‖⁻¹ *
        ‖heatOfHigh m G σ - heatOfHigh m G τ - (σ - τ) • heatH m τ (lapH m G)‖
      = (eLpNorm (fun ξ =>
          (((‖σ - τ‖⁻¹ *
              (gauss σ ξ - gauss τ ξ
                - (σ - τ) * (-(4 * π ^ 2 * ‖ξ‖ ^ 2) * gauss τ ξ)) : ℝ) : ℂ) •
            (G : E3 → V) ξ)) 2 (μw m)).toReal := by
  set remF :=
    heatOfHigh m G σ - heatOfHigh m G τ - (σ - τ) • heatH m τ (lapH m G)
  have hnorm : ‖σ - τ‖⁻¹ * ‖remF‖ = ‖(‖σ - τ‖⁻¹ : ℝ) • remF‖ := by
    rw [norm_smul]
    have : ‖(‖σ - τ‖⁻¹ : ℝ)‖ = ‖σ - τ‖⁻¹ :=
      abs_of_nonneg (inv_nonneg.2 (norm_nonneg _))
    rw [this]
  rw [hnorm]
  have hfun :
      ⇑((‖σ - τ‖⁻¹ : ℝ) • remF) =ᵐ[μw m]
        fun ξ =>
          (((‖σ - τ‖⁻¹ *
              (gauss σ ξ - gauss τ ξ
                - (σ - τ) * (-(4 * π ^ 2 * ‖ξ‖ ^ 2) * gauss τ ξ)) : ℝ) : ℂ) •
            (G : E3 → V) ξ) := by
    filter_upwards [coeFn_real_smul_Hm m (‖σ - τ‖⁻¹) remF,
      coeFn_heat_remainder m G σ τ] with ξ h1 h2
    rw [h1, h2, smul_smul, ← Complex.ofReal_mul]
  rw [← eLpNorm_congr_ae hfun]
  rfl

/-- For `G ∈ Ĥ^{m+2}` and `τ ≥ 0`, the curve `σ ↦ e^{σΔ} G` in `Ĥ^m`
has a one-sided derivative at `τ` along `[0, ∞)`, equal to `e^{τΔ}(Δ G)`. -/
theorem hasDerivWithinAt_heatH (m : ℕ) (G : Hm (m + 2)) {τ : ℝ} (hτ : 0 ≤ τ) :
    HasDerivWithinAt (heatOfHigh m G) (heatH m τ (lapH m G)) (Ici (0 : ℝ)) τ := by
  rw [hasDerivWithinAt_iff_tendsto]
  have hg : Measurable (G : E3 → V) := (Lp.stronglyMeasurable G).measurable
  let remSc : ℝ → E3 → ℝ := fun σ ξ =>
    gauss σ ξ - gauss τ ξ - (σ - τ) * (-(4 * π ^ 2 * ‖ξ‖ ^ 2) * gauss τ ξ)
  let slope : ℝ → E3 → V := fun σ ξ =>
    (((‖σ - τ‖⁻¹ * remSc σ ξ : ℝ) : ℂ) • (G : E3 → V) ξ)
  have hnorm : ∀ σ,
      ‖σ - τ‖⁻¹ *
          ‖heatOfHigh m G σ - heatOfHigh m G τ - (σ - τ) • heatH m τ (lapH m G)‖
        = (eLpNorm (slope σ) 2 (μw m)).toReal :=
    fun σ => norm_heat_slope m G σ τ
  have hlim :
      Tendsto (fun σ => ∫⁻ ξ, ‖slope σ ξ‖ₑ ^ ((2 : ENNReal).toReal) ∂(μw m))
        (𝓝[Ici (0 : ℝ)] τ) (𝓝 0) := by
    have hDC := MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence (μ := μw m)
      (l := 𝓝[Ici (0 : ℝ)] τ) (f := fun _ => 0)
      (F := fun σ ξ => ‖slope σ ξ‖ₑ ^ ((2 : ENNReal).toReal))
      (fun ξ => (ENNReal.ofReal (2 * (4 * π ^ 2 * ‖ξ‖ ^ 2)) *
          ‖(G : E3 → V) ξ‖ₑ) ^ ((2 : ENNReal).toReal))
      (Eventually.of_forall fun σ => by
        have hc : Continuous fun ξ : E3 => ((‖σ - τ‖⁻¹ * remSc σ ξ : ℝ) : ℂ) :=
          Complex.continuous_ofReal.comp
            (continuous_const.mul (continuous_gauss_remainder σ τ))
        exact ((hc.measurable.smul hg).enorm).pow_const _)
      (eventually_mem_nhdsWithin.mono fun σ hσ =>
        Eventually.of_forall fun ξ => by
          have hle := rem_div_le (Set.mem_Ici.1 hσ) hτ ξ
          refine ENNReal.rpow_le_rpow ?_ (by norm_num)
          rw [show slope σ ξ =
              (((‖σ - τ‖⁻¹ * remSc σ ξ : ℝ) : ℂ) • (G : E3 → V) ξ) from rfl,
            enorm_slope_eq σ τ ξ]
          exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hle) (zero_le _))
      (lintegral_dom_lt_top m G).ne
      (Eventually.of_forall fun ξ => by
        have hder :=
          (hasDerivWithinAt_iff_tendsto.1 (hasDerivWithinAt_gauss ξ hτ))
        have hlin : Continuous fun r : ℝ => r * ‖(G : E3 → V) ξ‖ :=
          continuous_id.mul continuous_const
        have hlin0 : Tendsto (fun r : ℝ => r * ‖(G : E3 → V) ξ‖) (𝓝 0) (𝓝 0) := by
          simpa using hlin.tendsto 0
        have h0 : Tendsto (fun r : ℝ => ENNReal.ofReal (r * ‖(G : E3 → V) ξ‖))
            (𝓝 0) (𝓝 0) := by
          have hcomp := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hlin0
          simpa using hcomp
        have hmul :
            Tendsto (fun σ =>
                ENNReal.ofReal (‖σ - τ‖⁻¹ * |remSc σ ξ|) * ‖(G : E3 → V) ξ‖ₑ)
              (𝓝[Ici (0 : ℝ)] τ) (𝓝 0) := by
          have hnn : ∀ σ, 0 ≤ ‖σ - τ‖⁻¹ * |remSc σ ξ| :=
            fun σ => mul_nonneg (inv_nonneg.2 (norm_nonneg _)) (abs_nonneg _)
          have hrew :
              (fun σ => ENNReal.ofReal (‖σ - τ‖⁻¹ * |remSc σ ξ|) * ‖(G : E3 → V) ξ‖ₑ) =
                (fun r : ℝ => ENNReal.ofReal (r * ‖(G : E3 → V) ξ‖)) ∘
                  fun σ => ‖σ - τ‖⁻¹ * |remSc σ ξ| := by
            ext σ
            rw [Function.comp_apply, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (hnn σ)]
          rw [hrew]
          exact h0.comp hder
        have hrpow :=
          (ENNReal.continuous_rpow_const (y := (2 : ENNReal).toReal)).tendsto 0 |>.comp hmul
        have hpow0 : (0 : ℝ≥0∞) ^ ((2 : ENNReal).toReal) = 0 :=
          ENNReal.zero_rpow_of_pos (by norm_num)
        rw [hpow0] at hrpow
        refine hrpow.congr fun σ => ?_
        change (ENNReal.ofReal (‖σ - τ‖⁻¹ * |remSc σ ξ|) * ‖(G : E3 → V) ξ‖ₑ) ^
            ((2 : ENNReal).toReal)
          = ‖(((‖σ - τ‖⁻¹ * remSc σ ξ : ℝ) : ℂ) • (G : E3 → V) ξ)‖ₑ ^
              ((2 : ENNReal).toReal)
        rw [enorm_slope_eq σ τ ξ])
    have hz : ∫⁻ _ : E3, (0 : ℝ≥0∞) ∂(μw m) = 0 := lintegral_zero
    simpa [hz] using hDC
  have h2 :=
    (ENNReal.continuous_rpow_const (y := 1 / (2 : ENNReal).toReal)).tendsto 0 |>.comp hlim
  have h3 : (0 : ENNReal) ^ (1 / (2 : ENNReal).toReal) = 0 :=
    ENNReal.zero_rpow_of_pos (by norm_num)
  rw [h3] at h2
  have hE :
      Tendsto (fun σ => eLpNorm (slope σ) 2 (μw m)) (𝓝[Ici (0 : ℝ)] τ) (𝓝 0) := by
    refine h2.congr fun σ => ?_
    simp only [Function.comp_apply]
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  have hR := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hE
  refine hR.congr fun σ => ?_
  simp only [Function.comp_apply]
  exact (hnorm σ).symm

/-- Viscosity scaling: `σ ↦ e^{νσ Δ} G` has one-sided derivative `ν e^{ντ Δ}(Δ G)` on `[0, ∞)`. -/
theorem hasDerivWithinAt_heatH_visc (m : ℕ) (ν : ℝ) (hν : 0 ≤ ν)
    (G : Hm (m + 2)) {τ : ℝ} (hτ : 0 ≤ τ) :
    HasDerivWithinAt (fun σ => heatOfHigh m G (ν * σ))
      (ν • heatH m (ν * τ) (lapH m G)) (Ici (0 : ℝ)) τ := by
  have hinner : HasDerivWithinAt (fun σ : ℝ => ν * σ) ν (Ici (0 : ℝ)) τ := by
    have h := ((hasDerivAt_id τ).const_mul ν).hasDerivWithinAt (s := Ici (0 : ℝ))
    convert h
    ring
  have hmap : MapsTo (fun σ : ℝ => ν * σ) (Ici (0 : ℝ)) (Ici (0 : ℝ)) :=
    fun σ hσ => mul_nonneg hν (Set.mem_Ici.1 hσ)
  have hheat := hasDerivWithinAt_heatH m G (mul_nonneg hν hτ)
  exact hheat.scomp τ hinner hmap

#print axioms HeatDeriv.lapH
#print axioms HeatDeriv.hasDerivWithinAt_gauss
#print axioms HeatDeriv.gauss_lip
#print axioms HeatDeriv.gauss_remainder_bound
#print axioms HeatDeriv.coeFn_heatOfHigh
#print axioms HeatDeriv.coeFn_heat_lapH
#print axioms HeatDeriv.rem_scalar_ofReal
#print axioms HeatDeriv.rem_div_le
#print axioms HeatDeriv.coeFn_real_smul_Hm
#print axioms HeatDeriv.coeFn_heat_remainder
#print axioms HeatDeriv.lintegral_dom_lt_top
#print axioms HeatDeriv.continuous_gauss_remainder
#print axioms HeatDeriv.enorm_slope_eq
#print axioms HeatDeriv.norm_heat_slope
#print axioms HeatDeriv.hasDerivWithinAt_heatH
#print axioms HeatDeriv.hasDerivWithinAt_heatH_visc

end HeatDeriv
