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
open ProductEstimate (Cw Cw_lt_top one_le_ω measurable_ω rpow_two' sq_rpow_half)

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

lemma aesm_coe_Hm {m : ℕ} (G : Hm m) :
    AEStronglyMeasurable (G : E3 → V) volume :=
  (Lp.stronglyMeasurable G).aestronglyMeasurable.mono_ac (ac_vol m)

/-- Half-powers of the Japanese bracket cancel: `ω^{m/2} · ω^{-m/2} = 1`. -/
lemma ω_pow_half_mul_inv (m : ℕ) (ξ : E3) :
    (ω ξ ^ m) ^ (1 / 2 : ℝ) * (ω ξ ^ m) ^ (-(1 / 2 : ℝ)) = 1 := by
  rw [ENNReal.rpow_neg]
  refine ENNReal.mul_inv_cancel ?_ ?_
  · exact (ENNReal.rpow_pos (ENNReal.pow_pos (lt_of_lt_of_le zero_lt_one (one_le_ω ξ)) m)
      (ω_pow_ne_top m ξ)).ne'
  · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ω_pow_ne_top m ξ)

lemma moment_A_mul_B {m n : ℕ} (G : Hm m) (ξ : E3) :
    (ENNReal.ofReal (‖ξ‖ ^ n) * (ω ξ ^ m) ^ (-(1 / 2 : ℝ))) *
        ((ω ξ ^ m) ^ (1 / 2 : ℝ) * ‖(G : E3 → V) ξ‖ₑ) =
      ENNReal.ofReal (‖ξ‖ ^ n) * ‖(G : E3 → V) ξ‖ₑ := by
  have h := ω_pow_half_mul_inv m ξ
  calc (ENNReal.ofReal (‖ξ‖ ^ n) * (ω ξ ^ m) ^ (-(1 / 2 : ℝ))) *
          ((ω ξ ^ m) ^ (1 / 2 : ℝ) * ‖(G : E3 → V) ξ‖ₑ)
      = ENNReal.ofReal (‖ξ‖ ^ n) *
          ((ω ξ ^ m) ^ (-(1 / 2 : ℝ)) * (ω ξ ^ m) ^ (1 / 2 : ℝ)) *
          ‖(G : E3 → V) ξ‖ₑ := by
        simp only [mul_assoc]
    _ = ENNReal.ofReal (‖ξ‖ ^ n) *
          ((ω ξ ^ m) ^ (1 / 2 : ℝ) * (ω ξ ^ m) ^ (-(1 / 2 : ℝ))) *
          ‖(G : E3 → V) ξ‖ₑ := by
        rw [mul_comm ((ω ξ ^ m) ^ (-(1 / 2 : ℝ)))]
    _ = ENNReal.ofReal (‖ξ‖ ^ n) * 1 * ‖(G : E3 → V) ξ‖ₑ := by rw [h]
    _ = ENNReal.ofReal (‖ξ‖ ^ n) * ‖(G : E3 → V) ξ‖ₑ := by rw [mul_one]

lemma moment_A_sq {m n : ℕ} (ξ : E3) :
    (ENNReal.ofReal (‖ξ‖ ^ n) * (ω ξ ^ m) ^ (-(1 / 2 : ℝ))) ^ 2 =
      ENNReal.ofReal (‖ξ‖ ^ (2 * n) / FourierEmb.w ξ ^ m) := by
  have hnn : 0 ≤ ‖ξ‖ ^ n := pow_nonneg (norm_nonneg _) n
  have hw : 0 < FourierEmb.w ξ ^ m := pow_pos (FourierEmb.w_pos ξ) m
  have hinv : ((ω ξ ^ m) ^ (-(1 / 2 : ℝ))) ^ 2 = (ω ξ ^ m)⁻¹ := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, Nat.cast_ofNat,
      show -(1 / 2 : ℝ) * (2 : ℝ) = (-1 : ℝ) by norm_num, ENNReal.rpow_neg_one]
  rw [mul_pow, ← ENNReal.ofReal_pow hnn, ← pow_mul, mul_comm n 2, hinv, ω_pow_eq_ofReal,
    ← ENNReal.ofReal_inv_of_pos hw, ← ENNReal.ofReal_mul (pow_nonneg (norm_nonneg _) (2 * n)),
    div_eq_mul_inv]

lemma moment_B_sq {m : ℕ} (G : Hm m) (ξ : E3) :
    ((ω ξ ^ m) ^ (1 / 2 : ℝ) * ‖(G : E3 → V) ξ‖ₑ) ^ 2 =
      ω ξ ^ m * ‖(G : E3 → V) ξ‖ₑ ^ 2 := by
  rw [mul_pow, sq_rpow_half]

lemma aemeasurable_moment_A (m n : ℕ) :
    AEMeasurable (fun ξ : E3 =>
      ENNReal.ofReal (‖ξ‖ ^ n) * (ω ξ ^ m) ^ (-(1 / 2 : ℝ))) volume :=
  ((continuous_pow n).comp continuous_norm).measurable.ennreal_ofReal.aemeasurable.mul
    ((measurable_ω.pow_const m).aemeasurable.pow_const _)

lemma aemeasurable_moment_B {m : ℕ} (G : Hm m) :
    AEMeasurable (fun ξ : E3 =>
      (ω ξ ^ m) ^ (1 / 2 : ℝ) * ‖(G : E3 → V) ξ‖ₑ) volume :=
  ((measurable_ω.pow_const m).aemeasurable.pow_const _).mul (aesm_coe_Hm G).enorm

/-- If `G ∈ Ĥ^m` and `m ≥ n + 2`, then `ξ ↦ ‖ξ‖^n ‖G ξ‖` is integrable. -/
theorem integrable_moment_of_Hm {m n : ℕ} (hm : n + 2 ≤ m) (G : Hm m) :
    Integrable (fun ξ : E3 => ‖ξ‖ ^ n * ‖(G : E3 → V) ξ‖) volume := by
  have hsm : AEStronglyMeasurable (fun ξ : E3 => ‖ξ‖ ^ n * ‖(G : E3 → V) ξ‖) volume :=
    ((continuous_pow n).comp continuous_norm).aestronglyMeasurable.mul (aesm_coe_Hm G).norm
  refine ⟨hsm, ?_⟩
  set A : E3 → ℝ≥0∞ :=
    fun ξ => ENNReal.ofReal (‖ξ‖ ^ n) * (ω ξ ^ m) ^ (-(1 / 2 : ℝ))
  set B : E3 → ℝ≥0∞ :=
    fun ξ => (ω ξ ^ m) ^ (1 / 2 : ℝ) * ‖(G : E3 → V) ξ‖ₑ
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ := volume)
    Real.HolderConjugate.two_two (aemeasurable_moment_A m n) (aemeasurable_moment_B G)
  have hlin : ∫⁻ ξ, ‖‖ξ‖ ^ n * ‖(G : E3 → V) ξ‖‖ₑ = ∫⁻ ξ, A ξ * B ξ := by
    refine (lintegral_congr fun ξ => ?_).trans
      (lintegral_congr fun ξ => (moment_A_mul_B (n := n) G ξ).symm)
    have hn : 0 ≤ ‖ξ‖ ^ n := pow_nonneg (norm_nonneg _) n
    rw [enorm_mul, Real.enorm_eq_ofReal hn, enorm_norm ((G : E3 → V) ξ)]
  have hAint : ∫⁻ ξ, A ξ ^ 2 = ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * n) / FourierEmb.w ξ ^ m) :=
    lintegral_congr fun ξ => moment_A_sq ξ
  have hBint : ∫⁻ ξ, B ξ ^ 2 ≤ ENNReal.ofReal ((2 : ℝ) ^ m) * eLpNorm G 2 (μw m) ^ 2 := by
    have hmono : ∫⁻ ξ, B ξ ^ 2 ≤
        ∫⁻ ξ, ENNReal.ofReal ((2 : ℝ) ^ m) * (sobW m ξ * ‖(G : E3 → V) ξ‖ₑ ^ 2) := by
      refine lintegral_mono fun ξ => ?_
      calc B ξ ^ 2
          = ω ξ ^ m * ‖(G : E3 → V) ξ‖ₑ ^ 2 := moment_B_sq G ξ
        _ ≤ (ENNReal.ofReal ((2 : ℝ) ^ m) * sobW m ξ) * ‖(G : E3 → V) ξ‖ₑ ^ 2 :=
            mul_le_mul_left (ω_pow_le_mul_sobW m ξ) _
        _ = ENNReal.ofReal ((2 : ℝ) ^ m) * (sobW m ξ * ‖(G : E3 → V) ξ‖ₑ ^ 2) := by
            rw [mul_assoc]
    refine hmono.trans (le_of_eq ?_)
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, eLpNorm_sq, lintegral_μw]
  have hAtop : ∫⁻ ξ, A ξ ^ 2 < ⊤ := by rw [hAint]; exact lintegral_xi_pow_div_w hm
  have hBtop : ∫⁻ ξ, B ξ ^ 2 < ⊤ :=
    hBint.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.pow_lt_top (Lp.eLpNorm_lt_top G)))
  have hAtopR : ∫⁻ ξ, A ξ ^ (2 : ℝ) < ⊤ := by
    have : ∫⁻ ξ, A ξ ^ (2 : ℝ) = ∫⁻ ξ, A ξ ^ 2 := lintegral_congr fun ξ => rpow_two' _
    rwa [this]
  have hBtopR : ∫⁻ ξ, B ξ ^ (2 : ℝ) < ⊤ := by
    have : ∫⁻ ξ, B ξ ^ (2 : ℝ) = ∫⁻ ξ, B ξ ^ 2 := lintegral_congr fun ξ => rpow_two' _
    rwa [this]
  have hfin : ∫⁻ ξ, (A * B) ξ < ⊤ :=
    hCS.trans_lt (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hAtopR.ne)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hBtopR.ne))
  have hAB : ∫⁻ ξ, A ξ * B ξ = ∫⁻ ξ, (A * B) ξ := rfl
  change ∫⁻ ξ, ‖‖ξ‖ ^ n * ‖(G : E3 → V) ξ‖‖ₑ < ⊤
  rw [hlin, hAB]
  exact hfin

/-- If `G ∈ Ĥ^m` and `m ≥ 2`, then `G` is (unweighted) integrable on ℝ³. -/
theorem integrable_of_Hm {m : ℕ} (hm : 2 ≤ m) (G : Hm m) :
    Integrable (G : E3 → V) volume := by
  have h := integrable_moment_of_Hm (n := 0) (by omega) G
  simp only [pow_zero, one_mul] at h
  refine ⟨aesm_coe_Hm G, ?_⟩
  simpa [HasFiniteIntegral, enorm_norm'] using h.2

lemma integrable_moment_comp_neg {m n : ℕ} (hm : n + 2 ≤ m) (G : Hm m) :
    Integrable (fun ξ : E3 => ‖ξ‖ ^ n * ‖(G : E3 → V) (-ξ)‖) volume := by
  have h := integrable_moment_of_Hm hm G
  have hmp : MeasurePreserving (Neg.neg : E3 → E3) volume volume :=
    Measure.measurePreserving_neg volume
  have heq : (fun ξ : E3 => ‖ξ‖ ^ n * ‖(G : E3 → V) (-ξ)‖) =
      (fun ξ : E3 => ‖ξ‖ ^ n * ‖(G : E3 → V) ξ‖) ∘ (Neg.neg : E3 → E3) := by
    funext ξ; simp [norm_neg]
  rw [heq]
  have hG : Integrable (fun ξ : E3 => ‖ξ‖ ^ n * ‖(G : E3 → V) ξ‖)
      (Measure.map (Neg.neg : E3 → E3) volume) := by
    rwa [hmp.map_eq]
  exact (integrable_map_measure hG.aestronglyMeasurable measurable_neg.aemeasurable).1 hG

/-- If `G ∈ Ĥ^m` and `m ≥ n + 2`, the inverse Fourier transform of `G` is `C^n`. -/
theorem contDiff_fourierInv_of_Hm {m n : ℕ} (hm : n + 2 ≤ m) (G : Hm m) :
    ContDiff ℝ n (𝓕⁻ (G : E3 → V)) := by
  rw [fourierInv_eq_fourier_comp_neg]
  refine contDiff_fourier ?_
  intro k hk
  have hkn : k ≤ n := Nat.cast_le.1 hk
  exact integrable_moment_comp_neg (le_trans (Nat.add_le_add_right hkn 2) hm) G

lemma fourierInv_congr_ae {f₁ f₂ : E3 → V} (h : f₁ =ᵐ[volume] f₂) (x : E3) :
    𝓕⁻ f₁ x = 𝓕⁻ f₂ x :=
  (fourierInv_eq_fourier_neg f₁ x).trans
    ((fourier_congr_ae h (-x)).trans (fourierInv_eq_fourier_neg f₂ x).symm)

/-- If a physical `L²` field has finite Fourier energy of every order, then
`𝓕⁻ (𝓕 F)` is `C^∞`. -/
theorem contDiff_fourierInv_of_all_energy {F : L2V}
    (h : ∀ k : ℕ, fourierEnergy k F < ⊤) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (𝓕⁻ ((𝓕 F : L2V) : E3 → V)) := by
  rw [contDiff_infty]
  intro n
  have hE : fourierEnergy (n + 2) F < ⊤ := h (n + 2)
  have hs := contDiff_fourierInv_of_Hm (m := n + 2) (n := n) le_rfl (toHm F hE)
  have haeμ : (toHm F hE : E3 → V) =ᵐ[μw (n + 2)] ((𝓕 F : L2V) : E3 → V) :=
    MemLp.coeFn_toLp (memLp_fourier_of_energy hE)
  have hae : (toHm F hE : E3 → V) =ᵐ[volume] ((𝓕 F : L2V) : E3 → V) :=
    haeμ.filter_mono (Measure.AbsolutelyContinuous.ae_le (ac_vol (n + 2)))
  have heq : 𝓕⁻ (toHm F hE : E3 → V) = 𝓕⁻ ((𝓕 F : L2V) : E3 → V) :=
    funext fun x => fourierInv_congr_ae hae x
  exact heq ▸ hs

#print axioms InverseSobolev.sobW_le_mul_ω_pow
#print axioms InverseSobolev.ω_pow_le_mul_sobW
#print axioms InverseSobolev.xi_pow_div_w
#print axioms InverseSobolev.lintegral_xi_pow_div_w
#print axioms InverseSobolev.integrable_moment_of_Hm
#print axioms InverseSobolev.integrable_of_Hm
#print axioms InverseSobolev.contDiff_fourierInv_of_Hm
#print axioms InverseSobolev.contDiff_fourierInv_of_all_energy

end InverseSobolev
