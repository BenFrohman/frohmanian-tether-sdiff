import Scratch.DuhamelUp
import Scratch.FourierEmbedding

/-! # Fourier-side `H³` product estimate (item 3, scalar `lintegral` form)

* `young_L1_L2`: `∫ (∫ f(ξ-η) g(η) dη)² dξ ≤ (∫ f)² ∫ g²` (`f, g ≥ 0`).
* weight inequality `w(ξ) ≤ 2 (w(ξ-η) + w(η))`, `w = 1 + 4π²|ξ|²`.
* `L¹` control `∫ |F| ≤ C (∫ w² |F|²)^{1/2}`. -/

open MeasureTheory Real
open scoped ENNReal

noncomputable section
namespace ProductEstimate

open LerayHeat

lemma sq_rpow_half (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

lemma rpow_two' (x : ℝ≥0∞) : x ^ (2 : ℝ) = x ^ 2 := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]

/-- Weighted Cauchy–Schwarz: `(∫ a b)² ≤ (∫ a)(∫ a b²)`. -/
lemma cs_weighted {α : Type*} [MeasurableSpace α] (μ : Measure α) {a b : α → ℝ≥0∞}
    (ha : AEMeasurable a μ) (hb : AEMeasurable b μ) :
    (∫⁻ x, a x * b x ∂μ) ^ 2 ≤ (∫⁻ x, a x ∂μ) * ∫⁻ x, a x * b x ^ 2 ∂μ := by
  have hA : AEMeasurable (fun x => a x ^ (1 / 2 : ℝ)) μ := ha.pow_const _
  have hB : AEMeasurable (fun x => a x ^ (1 / 2 : ℝ) * b x) μ := hA.mul hb
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hA hB
  have e1 : ∀ x, (fun x => a x ^ (1 / 2 : ℝ)) x * (fun x => a x ^ (1 / 2 : ℝ) * b x) x = a x * b x :=
    fun x => by simp only; rw [← mul_assoc, ← sq, sq_rpow_half]
  have e2 : ∀ x, (a x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = a x := fun x => by rw [rpow_two', sq_rpow_half]
  have e3 : ∀ x, (a x ^ (1 / 2 : ℝ) * b x) ^ (2 : ℝ) = a x * b x ^ 2 := fun x => by
    rw [rpow_two', mul_pow, sq_rpow_half]
  simp only [Pi.mul_apply, e1, e2, e3] at h
  calc (∫⁻ x, a x * b x ∂μ) ^ 2
      ≤ ((∫⁻ x, a x ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ x, a x * b x ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (zero_le _) h 2
    _ = _ := by rw [mul_pow, sq_rpow_half, sq_rpow_half]

/-- **Young's inequality** `L¹ * L² → L²` on ℝ³ (nonnegative `lintegral` form). -/
theorem young_L1_L2 {f g : E3 → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ ξ, (∫⁻ η, f (ξ - η) * g η) ^ 2 ≤ (∫⁻ x, f x) ^ 2 * ∫⁻ x, g x ^ 2 := by
  have hpt : ∀ ξ, (∫⁻ η, f (ξ - η) * g η) ^ 2 ≤
      (∫⁻ x, f x) * ∫⁻ η, f (ξ - η) * g η ^ 2 := fun ξ => by
    have := cs_weighted volume ((hf.comp (measurable_const.sub measurable_id)).aemeasurable)
      hg.aemeasurable (a := fun η => f (ξ - η)) (b := g)
    rwa [lintegral_sub_left_eq_self (fun x => f x) ξ] at this
  calc ∫⁻ ξ, (∫⁻ η, f (ξ - η) * g η) ^ 2
      ≤ ∫⁻ ξ, (∫⁻ x, f x) * ∫⁻ η, f (ξ - η) * g η ^ 2 := lintegral_mono hpt
    _ = (∫⁻ x, f x) * ∫⁻ ξ, ∫⁻ η, f (ξ - η) * g η ^ 2 :=
        lintegral_const_mul _ (Measurable.lintegral_prod_right'
          (f := fun p : E3 × E3 => f (p.1 - p.2) * g p.2 ^ 2)
          ((hf.comp measurable_sub).mul ((hg.comp measurable_snd).pow_const 2)))
    _ = (∫⁻ x, f x) * ∫⁻ η, ∫⁻ ξ, f (ξ - η) * g η ^ 2 := by
        rw [lintegral_lintegral_swap ((hf.comp measurable_sub).aemeasurable.mul
          ((hg.comp measurable_snd).pow_const 2).aemeasurable)]
    _ = (∫⁻ x, f x) * ∫⁻ η, (∫⁻ x, f x) * g η ^ 2 := by
        congr 1; refine lintegral_congr fun η => ?_
        rw [lintegral_mul_const (g η ^ 2) (show Measurable fun ξ => f (ξ - η) from
          hf.comp (measurable_id.sub measurable_const)),
          lintegral_sub_right_eq_self (fun x => f x) η]
    _ = (∫⁻ x, f x) ^ 2 * ∫⁻ x, g x ^ 2 := by
        rw [lintegral_const_mul _ (hg.pow_const 2), ← mul_assoc, sq]

/-! ## Weights -/

/-- `ω(ξ) = 1 + 4π²|ξ|²` as an extended real. -/
def ω (ξ : E3) : ℝ≥0∞ := ENNReal.ofReal (FourierEmb.w ξ)

lemma measurable_ω : Measurable ω := by
  unfold ω FourierEmb.w; fun_prop

lemma w_le (ξ η : E3) : FourierEmb.w ξ ≤ 2 * (FourierEmb.w (ξ - η) + FourierEmb.w η) := by
  unfold FourierEmb.w
  have h1 : ‖ξ‖ ≤ ‖ξ - η‖ + ‖η‖ := by
    calc ‖ξ‖ = ‖(ξ - η) + η‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have h2 : ‖ξ‖ ^ 2 ≤ 2 * ‖ξ - η‖ ^ 2 + 2 * ‖η‖ ^ 2 := by
    nlinarith [norm_nonneg ξ, norm_nonneg (ξ - η), norm_nonneg η, sq_nonneg (‖ξ - η‖ - ‖η‖)]
  have hc : 0 ≤ (2 * π) ^ 2 := by positivity
  nlinarith

/-- `v = ω^{3/2}` (the `H³` weight). -/
def v (ξ : E3) : ℝ≥0∞ := ω ξ ^ (3 / 2 : ℝ)

lemma measurable_v : Measurable v := measurable_ω.pow_const _

lemma v_ne_top (ξ : E3) : v ξ ≠ ⊤ :=
  ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top

lemma v_sq (ξ : E3) : v ξ ^ 2 = ω ξ ^ 3 := by
  rw [v, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_natCast]; norm_num

lemma v_le (ξ η : E3) : v ξ ≤ 8 * (v (ξ - η) + v η) := by
  have h : ω ξ ≤ 4 * max (ω (ξ - η)) (ω η) := by
    unfold ω
    rw [← ENNReal.ofReal_max, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ((w_le ξ η).trans ?_)
    have := le_max_left (FourierEmb.w (ξ - η)) (FourierEmb.w η)
    have := le_max_right (FourierEmb.w (ξ - η)) (FourierEmb.w η)
    linarith
  have h8 : (4 : ℝ≥0∞) ^ (3 / 2 : ℝ) = 8 := by
    rw [show (4 : ℝ≥0∞) = 2 ^ (2 : ℝ) by norm_num, ← ENNReal.rpow_mul]; norm_num
  calc v ξ ≤ (4 * max (ω (ξ - η)) (ω η)) ^ (3 / 2 : ℝ) := ENNReal.rpow_le_rpow h (by norm_num)
    _ = 8 * max (v (ξ - η)) (v η) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), h8]
        congr 1
        rcases le_total (ω (ξ - η)) (ω η) with h' | h'
        · rw [max_eq_right h']
          exact (max_eq_right (ENNReal.rpow_le_rpow h' (by norm_num : (0 : ℝ) ≤ 3 / 2))).symm
        · rw [max_eq_left h']
          exact (max_eq_left (ENNReal.rpow_le_rpow h' (by norm_num : (0 : ℝ) ≤ 3 / 2))).symm
    _ ≤ 8 * (v (ξ - η) + v η) := by
        gcongr; exact max_le le_self_add le_add_self

lemma add_sq_le (x y : ℝ≥0∞) : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · simp
  rcases eq_or_ne y ⊤ with rfl | hy
  · simp
  lift x to NNReal using hx
  lift y to NNReal using hy
  norm_cast
  rw [← NNReal.coe_le_coe]; push_cast
  nlinarith [sq_nonneg ((x : ℝ) - y)]

/-- **Weighted product estimate** (Fourier side of `‖fg‖_{H³} ≲ ‖f‖_{H³}‖g‖_{L^∞-type}`):
`∫ ω³ (F * G)² ≤ 128 ((∫G)² ∫ ω³F² + (∫F)² ∫ ω³G²)`. -/
theorem weighted_conv_le {F G : E3 → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G) :
    ∫⁻ ξ, ω ξ ^ 3 * (∫⁻ η, F (ξ - η) * G η) ^ 2 ≤
      128 * ((∫⁻ x, G x) ^ 2 * (∫⁻ x, ω x ^ 3 * F x ^ 2) +
        (∫⁻ x, F x) ^ 2 * (∫⁻ x, ω x ^ 3 * G x ^ 2)) := by
  have hvF : Measurable fun x => v x * F x := measurable_v.mul hF
  have hvG : Measurable fun x => v x * G x := measurable_v.mul hG
  have hpt : ∀ ξ, ω ξ ^ 3 * (∫⁻ η, F (ξ - η) * G η) ^ 2 ≤
      128 * ((∫⁻ η, G (ξ - η) * (v η * F η)) ^ 2 + (∫⁻ η, F (ξ - η) * (v η * G η)) ^ 2) := by
    intro ξ
    have e1 : ∫⁻ η, v (ξ - η) * F (ξ - η) * G η = ∫⁻ η, G (ξ - η) * (v η * F η) := by
      have := lintegral_sub_left_eq_self (μ := volume)
        (fun z => v z * F z * G (ξ - z)) ξ
      simp only [sub_sub_cancel] at this
      rw [this]; refine lintegral_congr fun z => by ring
    have hm1 : Measurable fun η => v (ξ - η) * F (ξ - η) * G η :=
      ((measurable_v.comp (measurable_const.sub measurable_id)).mul
        (hF.comp (measurable_const.sub measurable_id))).mul hG
    have hle : v ξ * ∫⁻ η, F (ξ - η) * G η ≤
        8 * ((∫⁻ η, G (ξ - η) * (v η * F η)) + ∫⁻ η, F (ξ - η) * (v η * G η)) := by
      calc v ξ * ∫⁻ η, F (ξ - η) * G η = ∫⁻ η, v ξ * (F (ξ - η) * G η) :=
            (lintegral_const_mul' _ _ (v_ne_top ξ)).symm
        _ ≤ ∫⁻ η, 8 * (v (ξ - η) * F (ξ - η) * G η + F (ξ - η) * (v η * G η)) := by
            refine lintegral_mono fun η => ?_
            calc v ξ * (F (ξ - η) * G η) ≤ 8 * (v (ξ - η) + v η) * (F (ξ - η) * G η) :=
                  mul_le_mul_left (v_le ξ η) _
              _ = _ := by ring
        _ = 8 * ((∫⁻ η, v (ξ - η) * F (ξ - η) * G η) + ∫⁻ η, F (ξ - η) * (v η * G η)) := by
            rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left hm1]
        _ = _ := by rw [e1]
    calc ω ξ ^ 3 * (∫⁻ η, F (ξ - η) * G η) ^ 2 = (v ξ * ∫⁻ η, F (ξ - η) * G η) ^ 2 := by
          rw [mul_pow, v_sq]
      _ ≤ (8 * ((∫⁻ η, G (ξ - η) * (v η * F η)) + ∫⁻ η, F (ξ - η) * (v η * G η))) ^ 2 :=
          pow_le_pow_left₀ (zero_le _) hle 2
      _ = 64 * ((∫⁻ η, G (ξ - η) * (v η * F η)) + ∫⁻ η, F (ξ - η) * (v η * G η)) ^ 2 := by
          rw [mul_pow]; norm_num
      _ ≤ 64 * (2 * (∫⁻ η, G (ξ - η) * (v η * F η)) ^ 2 +
            2 * (∫⁻ η, F (ξ - η) * (v η * G η)) ^ 2) := mul_le_mul_right (add_sq_le _ _) _
      _ = _ := by ring
  have hmeas1 : Measurable fun ξ => (∫⁻ η, G (ξ - η) * (v η * F η)) ^ 2 :=
    (Measurable.lintegral_prod_right' (f := fun p : E3 × E3 => G (p.1 - p.2) * (v p.2 * F p.2))
      ((hG.comp measurable_sub).mul (hvF.comp measurable_snd))).pow_const 2
  calc ∫⁻ ξ, ω ξ ^ 3 * (∫⁻ η, F (ξ - η) * G η) ^ 2
      ≤ ∫⁻ ξ, 128 * ((∫⁻ η, G (ξ - η) * (v η * F η)) ^ 2 +
          (∫⁻ η, F (ξ - η) * (v η * G η)) ^ 2) := lintegral_mono hpt
    _ = 128 * ((∫⁻ ξ, (∫⁻ η, G (ξ - η) * (v η * F η)) ^ 2) +
          ∫⁻ ξ, (∫⁻ η, F (ξ - η) * (v η * G η)) ^ 2) := by
        rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left hmeas1]
    _ ≤ 128 * ((∫⁻ x, G x) ^ 2 * (∫⁻ x, (v x * F x) ^ 2) +
          (∫⁻ x, F x) ^ 2 * (∫⁻ x, (v x * G x) ^ 2)) := by
        exact mul_le_mul_right (add_le_add (young_L1_L2 hG hvF) (young_L1_L2 hF hvG)) _
    _ = _ := by
        simp only [mul_pow, v_sq]

/-- `C_w = ∫ (1 + 4π²|ξ|²)^{-2} dξ < ∞`. -/
def Cw : ℝ≥0∞ := ∫⁻ ξ : E3, ENNReal.ofReal (FourierEmb.w ξ)⁻¹ ^ (2 : ℝ)

lemma Cw_lt_top : Cw < ⊤ := FourierEmb.lintegral_w_inv_sq_lt_top

lemma one_le_ω (ξ : E3) : 1 ≤ ω ξ := by
  unfold ω FourierEmb.w
  rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg ‖ξ‖, pi_pos])

lemma winv_mul_ω (ξ : E3) : ENNReal.ofReal (FourierEmb.w ξ)⁻¹ ^ 2 * ω ξ ^ 2 = 1 := by
  rw [ω, ← mul_pow, ← ENNReal.ofReal_mul (inv_nonneg.2 (FourierEmb.w_pos ξ).le),
    inv_mul_cancel₀ (FourierEmb.w_pos ξ).ne', ENNReal.ofReal_one, one_pow]

/-- **`L¹` control from the `H³` weight**: `(∫ F)² ≤ C_w ∫ ω³ F²`. -/
theorem lintegral_sq_le {F : E3 → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ x, F x) ^ 2 ≤ Cw * ∫⁻ x, ω x ^ 3 * F x ^ 2 := by
  have ha : Measurable fun x => ENNReal.ofReal (FourierEmb.w x)⁻¹ ^ 2 := by
    unfold FourierEmb.w; fun_prop
  have h := cs_weighted volume ha.aemeasurable ((measurable_ω.pow_const 2).mul hF).aemeasurable
  have e1 : ∀ x, ENNReal.ofReal (FourierEmb.w x)⁻¹ ^ 2 * (ω x ^ 2 * F x) = F x := fun x => by
    rw [← mul_assoc, winv_mul_ω, one_mul]
  have e2 : ∀ x, ENNReal.ofReal (FourierEmb.w x)⁻¹ ^ 2 * (ω x ^ 2 * F x) ^ 2 = ω x ^ 2 * F x ^ 2 :=
    fun x => by
      rw [mul_pow, ← pow_mul, show ω x ^ (2 * 2) = ω x ^ 2 * ω x ^ 2 by ring, ← mul_assoc,
        ← mul_assoc, winv_mul_ω, one_mul]
  simp only [e1, e2] at h
  have hCw : ∫⁻ x, ENNReal.ofReal (FourierEmb.w x)⁻¹ ^ 2 = Cw := by
    unfold Cw; simp only [rpow_two']
  rw [hCw] at h
  refine h.trans (mul_le_mul_right (lintegral_mono fun x => ?_) _)
  refine mul_le_mul_left ?_ _
  calc ω x ^ 2 = ω x ^ 2 * 1 := (mul_one _).symm
    _ ≤ ω x ^ 2 * ω x := mul_le_mul_right (one_le_ω x) _
    _ = ω x ^ 3 := by ring

/-- **`H³` algebra estimate (Fourier side)**: `∫ ω³ (F * G)² ≤ 256 C_w (∫ ω³F²)(∫ ω³G²)`. -/
theorem weighted_conv_le_H3 {F G : E3 → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G) :
    ∫⁻ ξ, ω ξ ^ 3 * (∫⁻ η, F (ξ - η) * G η) ^ 2 ≤
      256 * Cw * ((∫⁻ x, ω x ^ 3 * F x ^ 2) * ∫⁻ x, ω x ^ 3 * G x ^ 2) := by
  refine (weighted_conv_le hF hG).trans ?_
  have h1 := lintegral_sq_le hG
  have h2 := lintegral_sq_le hF
  calc 128 * ((∫⁻ x, G x) ^ 2 * (∫⁻ x, ω x ^ 3 * F x ^ 2) +
        (∫⁻ x, F x) ^ 2 * (∫⁻ x, ω x ^ 3 * G x ^ 2))
      ≤ 128 * ((Cw * ∫⁻ x, ω x ^ 3 * G x ^ 2) * (∫⁻ x, ω x ^ 3 * F x ^ 2) +
        (Cw * ∫⁻ x, ω x ^ 3 * F x ^ 2) * (∫⁻ x, ω x ^ 3 * G x ^ 2)) :=
        mul_le_mul_right (add_le_add (mul_le_mul_left h1 _) (mul_le_mul_left h2 _)) _
    _ = _ := by ring

/-- Comparison of `sobW 3` (the exact `H³` weight) with `ω³`: `sobW 3 ≤ ω³ ≤ 4 sobW 3`. -/
theorem sobW3_le_ω3 (ξ : E3) : SobolevFourier.sobW 3 ξ ≤ ω ξ ^ 3 ∧ ω ξ ^ 3 ≤ 4 * SobolevFourier.sobW 3 ξ := by
  rw [SobolevFourier.sobW_eq, ω, ← ENNReal.ofReal_pow (FourierEmb.w_pos ξ).le]
  have ha : 0 ≤ 4 * π ^ 2 * ‖ξ‖ ^ 2 := by positivity
  have hw : FourierEmb.w ξ = 1 + 4 * π ^ 2 * ‖ξ‖ ^ 2 := by unfold FourierEmb.w; ring
  set a := 4 * π ^ 2 * ‖ξ‖ ^ 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hw]
  constructor
  · exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg a, pow_nonneg ha 3])
  · rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg a, pow_nonneg ha 3, sq_nonneg (a - 1)])

end ProductEstimate

#print axioms ProductEstimate.young_L1_L2
#print axioms ProductEstimate.weighted_conv_le
#print axioms ProductEstimate.lintegral_sq_le
#print axioms ProductEstimate.weighted_conv_le_H3
#print axioms ProductEstimate.sobW3_le_ω3
