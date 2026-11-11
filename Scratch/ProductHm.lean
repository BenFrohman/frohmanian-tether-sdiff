import Scratch.ProductEstimate
import Scratch.InverseSobolev
import Scratch.ProductH3
import Mathlib.Analysis.Convolution

/-! # Tame product estimates on `Ĥ^m` for all `m ≥ 3`

Fourier-side convolution bound with weight `ω^m`, and the tame form
`∫ ω^m (F*G)² ≤ C_m C_w ((∫ ω³ G²)(∫ ω^m F²) + (∫ ω³ F²)(∫ ω^m G²))`,
which on `Ĥ^m` yields
`‖F ⋆[L] G‖_{Ĥ^m} ≤ C_m ‖L‖ (‖F‖_{Ĥ^m} ‖G‖_{Ĥ³} + ‖F‖_{Ĥ³} ‖G‖_{Ĥ^m})`. -/

open MeasureTheory Real Filter Topology
open scoped ENNReal Convolution

set_option autoImplicit false

noncomputable section
namespace ProductHm

open LerayHeat SobolevFourier SobolevHilbert
open ProductEstimate (Cw Cw_lt_top one_le_ω measurable_ω rpow_two' sq_rpow_half
  w_le lintegral_sq_le sobW3_le_ω3 add_sq_le young_L1_L2)
open InverseSobolev (sobW_le_mul_ω_pow ω_pow_le_mul_sobW integrable_of_Hm)
open ProductH3 (Cstar Cstar_nonneg lintegral_ω3_enorm_sq)

abbrev ω := ProductEstimate.ω

/-! ## Weight inequalities for `ω^s` -/

lemma ω_le_four_max (ξ η : E3) : ω ξ ≤ 4 * max (ω (ξ - η)) (ω η) := by
  unfold ω ProductEstimate.ω
  rw [← ENNReal.ofReal_max, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ((w_le ξ η).trans ?_)
  have := le_max_left (FourierEmb.w (ξ - η)) (FourierEmb.w η)
  have := le_max_right (FourierEmb.w (ξ - η)) (FourierEmb.w η)
  linarith

/-- `v_s = ω^{s/2}`. -/
def vs (s : ℕ) (ξ : E3) : ℝ≥0∞ := ω ξ ^ (s / 2 : ℝ)

lemma measurable_vs (s : ℕ) : Measurable (vs s) := measurable_ω.pow_const _

lemma vs_ne_top (s : ℕ) (ξ : E3) : vs s ξ ≠ ⊤ :=
  ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top

lemma vs_sq (s : ℕ) (ξ : E3) : vs s ξ ^ 2 = ω ξ ^ s := by
  rw [vs, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, Nat.cast_ofNat,
    show (s / 2 : ℝ) * (2 : ℝ) = (s : ℝ) by ring, ENNReal.rpow_natCast]

lemma four_pow_half_sq (s : ℕ) :
    ((4 : ℝ≥0∞) ^ (s / 2 : ℝ)) ^ 2 = 4 ^ s := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, Nat.cast_ofNat,
    show (s / 2 : ℝ) * (2 : ℝ) = (s : ℝ) by ring, ENNReal.rpow_natCast]

/-- `ω(ξ)^{s/2} ≤ 4^{s/2} (ω(ξ-η)^{s/2} + ω(η)^{s/2})`. -/
lemma vs_le (s : ℕ) (ξ η : E3) :
    vs s ξ ≤ (4 : ℝ≥0∞) ^ (s / 2 : ℝ) * (vs s (ξ - η) + vs s η) := by
  have h := ω_le_four_max ξ η
  have hs : 0 ≤ (s / 2 : ℝ) := by positivity
  calc vs s ξ ≤ (4 * max (ω (ξ - η)) (ω η)) ^ (s / 2 : ℝ) :=
        ENNReal.rpow_le_rpow h hs
    _ = (4 : ℝ≥0∞) ^ (s / 2 : ℝ) * max (vs s (ξ - η)) (vs s η) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hs, vs, vs]
        congr 1
        rcases le_total (ω (ξ - η)) (ω η) with h' | h'
        · rw [max_eq_right h']
          exact (max_eq_right (ENNReal.rpow_le_rpow h' hs)).symm
        · rw [max_eq_left h']
          exact (max_eq_left (ENNReal.rpow_le_rpow h' hs)).symm
    _ ≤ (4 : ℝ≥0∞) ^ (s / 2 : ℝ) * (vs s (ξ - η) + vs s η) := by
        gcongr; exact max_le le_self_add le_add_self

/-- The constant `2 · 4^s` in the unweighted-to-weighted Young bound. -/
def Ks (s : ℕ) : ℝ≥0∞ := 2 * 4 ^ s

lemma Ks_eq (s : ℕ) : Ks s = 2 * ((4 : ℝ≥0∞) ^ (s / 2 : ℝ)) ^ 2 := by
  unfold Ks; rw [four_pow_half_sq]

lemma Ks_ne_top (s : ℕ) : Ks s ≠ ⊤ :=
  ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top (by norm_num))

/-- **Weighted product estimate** for every order `s`:
`∫ ω^s (F*G)² ≤ 2·4^s ((∫G)² ∫ ω^s F² + (∫F)² ∫ ω^s G²)`. -/
theorem weighted_conv_le_pow (s : ℕ) {F G : E3 → ℝ≥0∞}
    (hF : Measurable F) (hG : Measurable G) :
    ∫⁻ ξ, ω ξ ^ s * (∫⁻ η, F (ξ - η) * G η) ^ 2 ≤
      Ks s * ((∫⁻ x, G x) ^ 2 * (∫⁻ x, ω x ^ s * F x ^ 2) +
        (∫⁻ x, F x) ^ 2 * (∫⁻ x, ω x ^ s * G x ^ 2)) := by
  have hvF : Measurable fun x => vs s x * F x := (measurable_vs s).mul hF
  have hvG : Measurable fun x => vs s x * G x := (measurable_vs s).mul hG
  set K : ℝ≥0∞ := (4 : ℝ≥0∞) ^ (s / 2 : ℝ)
  have hK2 : K ^ 2 = 4 ^ s := four_pow_half_sq s
  have hpt : ∀ ξ, ω ξ ^ s * (∫⁻ η, F (ξ - η) * G η) ^ 2 ≤
      Ks s * ((∫⁻ η, G (ξ - η) * (vs s η * F η)) ^ 2 +
        (∫⁻ η, F (ξ - η) * (vs s η * G η)) ^ 2) := by
    intro ξ
    have e1 : ∫⁻ η, vs s (ξ - η) * F (ξ - η) * G η =
        ∫⁻ η, G (ξ - η) * (vs s η * F η) := by
      have := lintegral_sub_left_eq_self (μ := volume)
        (fun z => vs s z * F z * G (ξ - z)) ξ
      simp only [sub_sub_cancel] at this
      rw [this]; refine lintegral_congr fun z => by ring
    have hm1 : Measurable fun η => vs s (ξ - η) * F (ξ - η) * G η :=
      (((measurable_vs s).comp (measurable_const.sub measurable_id)).mul
        (hF.comp (measurable_const.sub measurable_id))).mul hG
    have hle : vs s ξ * ∫⁻ η, F (ξ - η) * G η ≤
        K * ((∫⁻ η, G (ξ - η) * (vs s η * F η)) +
          ∫⁻ η, F (ξ - η) * (vs s η * G η)) := by
      calc vs s ξ * ∫⁻ η, F (ξ - η) * G η
          = ∫⁻ η, vs s ξ * (F (ξ - η) * G η) :=
            (lintegral_const_mul' _ _ (vs_ne_top s ξ)).symm
        _ ≤ ∫⁻ η, K * (vs s (ξ - η) * F (ξ - η) * G η +
              F (ξ - η) * (vs s η * G η)) := by
            refine lintegral_mono fun η => ?_
            calc vs s ξ * (F (ξ - η) * G η)
                ≤ K * (vs s (ξ - η) + vs s η) * (F (ξ - η) * G η) :=
                  mul_le_mul_left (vs_le s ξ η) _
              _ = _ := by ring
        _ = K * ((∫⁻ η, vs s (ξ - η) * F (ξ - η) * G η) +
              ∫⁻ η, F (ξ - η) * (vs s η * G η)) := by
            have hKtop : K ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity)
              (by norm_num)
            rw [lintegral_const_mul' _ _ hKtop, lintegral_add_left hm1]
        _ = _ := by rw [e1]
    calc ω ξ ^ s * (∫⁻ η, F (ξ - η) * G η) ^ 2
        = (vs s ξ * ∫⁻ η, F (ξ - η) * G η) ^ 2 := by rw [mul_pow, vs_sq]
      _ ≤ (K * ((∫⁻ η, G (ξ - η) * (vs s η * F η)) +
            ∫⁻ η, F (ξ - η) * (vs s η * G η))) ^ 2 :=
          pow_le_pow_left₀ (zero_le _) hle 2
      _ = K ^ 2 * ((∫⁻ η, G (ξ - η) * (vs s η * F η)) +
            ∫⁻ η, F (ξ - η) * (vs s η * G η)) ^ 2 := by
          rw [mul_pow]
      _ ≤ K ^ 2 * (2 * (∫⁻ η, G (ξ - η) * (vs s η * F η)) ^ 2 +
            2 * (∫⁻ η, F (ξ - η) * (vs s η * G η)) ^ 2) :=
          mul_le_mul_right (add_sq_le _ _) _
      _ = Ks s * ((∫⁻ η, G (ξ - η) * (vs s η * F η)) ^ 2 +
            (∫⁻ η, F (ξ - η) * (vs s η * G η)) ^ 2) := by
          rw [Ks_eq, hK2]; ring
  have hmeas1 : Measurable fun ξ => (∫⁻ η, G (ξ - η) * (vs s η * F η)) ^ 2 :=
    (Measurable.lintegral_prod_right'
      (f := fun p : E3 × E3 => G (p.1 - p.2) * (vs s p.2 * F p.2))
      ((hG.comp measurable_sub).mul (hvF.comp measurable_snd))).pow_const 2
  calc ∫⁻ ξ, ω ξ ^ s * (∫⁻ η, F (ξ - η) * G η) ^ 2
      ≤ ∫⁻ ξ, Ks s * ((∫⁻ η, G (ξ - η) * (vs s η * F η)) ^ 2 +
          (∫⁻ η, F (ξ - η) * (vs s η * G η)) ^ 2) := lintegral_mono hpt
    _ = Ks s * ((∫⁻ ξ, (∫⁻ η, G (ξ - η) * (vs s η * F η)) ^ 2) +
          ∫⁻ ξ, (∫⁻ η, F (ξ - η) * (vs s η * G η)) ^ 2) := by
        rw [lintegral_const_mul' _ _ (Ks_ne_top s), lintegral_add_left hmeas1]
    _ ≤ Ks s * ((∫⁻ x, G x) ^ 2 * (∫⁻ x, (vs s x * F x) ^ 2) +
          (∫⁻ x, F x) ^ 2 * (∫⁻ x, (vs s x * G x) ^ 2)) :=
        mul_le_mul_right (add_le_add (young_L1_L2 hG hvF) (young_L1_L2 hF hvG)) _
    _ = Ks s * ((∫⁻ x, G x) ^ 2 * (∫⁻ x, ω x ^ s * F x ^ 2) +
          (∫⁻ x, F x) ^ 2 * (∫⁻ x, ω x ^ s * G x ^ 2)) := by
        congr 3 <;> (refine lintegral_congr fun x => ?_; rw [mul_pow, vs_sq])

/-- **Tame weighted estimate**: L¹ factors are controlled by the `H³` weight. -/
theorem weighted_conv_tame (s : ℕ) {F G : E3 → ℝ≥0∞}
    (hF : Measurable F) (hG : Measurable G) :
    ∫⁻ ξ, ω ξ ^ s * (∫⁻ η, F (ξ - η) * G η) ^ 2 ≤
      Ks s * Cw * ((∫⁻ x, ω x ^ 3 * G x ^ 2) * (∫⁻ x, ω x ^ s * F x ^ 2) +
        (∫⁻ x, ω x ^ 3 * F x ^ 2) * (∫⁻ x, ω x ^ s * G x ^ 2)) := by
  refine (weighted_conv_le_pow s hF hG).trans ?_
  have h1 := lintegral_sq_le hG
  have h2 := lintegral_sq_le hF
  calc Ks s * ((∫⁻ x, G x) ^ 2 * (∫⁻ x, ω x ^ s * F x ^ 2) +
        (∫⁻ x, F x) ^ 2 * (∫⁻ x, ω x ^ s * G x ^ 2))
      ≤ Ks s * ((Cw * ∫⁻ x, ω x ^ 3 * G x ^ 2) * (∫⁻ x, ω x ^ s * F x ^ 2) +
          (Cw * ∫⁻ x, ω x ^ 3 * F x ^ 2) * (∫⁻ x, ω x ^ s * G x ^ 2)) :=
        mul_le_mul_right (add_le_add (mul_le_mul_left h1 _) (mul_le_mul_left h2 _)) _
    _ = Ks s * Cw * ((∫⁻ x, ω x ^ 3 * G x ^ 2) * (∫⁻ x, ω x ^ s * F x ^ 2) +
          (∫⁻ x, ω x ^ 3 * F x ^ 2) * (∫⁻ x, ω x ^ s * G x ^ 2)) := by
        ring


/-! ## Constants for the tame `Ĥ^m` bound -/

/-- Squared tame constant `(s+1) · 8^{s+1} C_w`. -/
def CmSq (s : ℕ) : ℝ≥0∞ := ENNReal.ofReal (s + 1 : ℝ) * (8 : ℝ≥0∞) ^ (s + 1) * Cw

lemma CmSq_lt_top (s : ℕ) : CmSq s < ⊤ :=
  ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.pow_lt_top (by norm_num))) Cw_lt_top

lemma CmSq_ne_top (s : ℕ) : CmSq s ≠ ⊤ := (CmSq_lt_top s).ne

/-- Real tame constant `√((s+1) 8^{s+1} C_w)`. -/
def Cm (s : ℕ) : ℝ := Real.sqrt ((s + 1 : ℝ) * (8 : ℝ) ^ (s + 1) * Cw.toReal)

lemma Cm_nonneg (s : ℕ) : 0 ≤ Cm s := Real.sqrt_nonneg _

lemma two_pow_ennreal (s : ℕ) : ENNReal.ofReal ((2 : ℝ) ^ s) = (2 : ℝ≥0∞) ^ s := by
  rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]

lemma two_mul_four_pow (s : ℕ) :
    (2 : ℝ≥0∞) ^ s * (4 : ℝ≥0∞) ^ s = (8 : ℝ≥0∞) ^ s := by
  rw [← mul_pow]; norm_num

lemma Cm_eq_sqrt (s : ℕ) : Real.sqrt (CmSq s).toReal = Cm s := by
  unfold Cm CmSq
  have hs : 0 ≤ (s + 1 : ℝ) := by positivity
  simp [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_ofReal hs]

/-! ## Weight comparisons on `Ĥ^s` -/

lemma coeFn_incl {m m' : ℕ} (h : m' ≤ m) (F : Hm m) :
    (incl h F : E3 → V) =ᵐ[μw m'] (F : E3 → V) := by
  unfold incl
  refine (coeFn_wmul (fun _ => ContinuousLinearMap.id ℂ V) (fun g hg => hg) 1 zero_le_one _ F).trans ?_
  exact Filter.Eventually.of_forall fun ξ => ContinuousLinearMap.id_apply ((F : E3 → V) ξ)

lemma coeFn_incl_vol {m m' : ℕ} (h : m' ≤ m) (F : Hm m) :
    (incl h F : E3 → V) =ᵐ[volume] (F : E3 → V) :=
  (coeFn_incl h F).filter_mono (Measure.AbsolutelyContinuous.ae_le (ac_vol m'))

lemma lintegral_ωs_enorm_sq (s : ℕ) (F : Hm s) :
    ∫⁻ ξ, ω ξ ^ s * ‖(F : E3 → V) ξ‖ₑ ^ 2 ≤
      (2 : ℝ≥0∞) ^ s * eLpNorm F 2 (μw s) ^ 2 := by
  have h : ∫⁻ ξ, ω ξ ^ s * ‖(F : E3 → V) ξ‖ₑ ^ 2 ≤
      ∫⁻ ξ, ENNReal.ofReal ((2 : ℝ) ^ s) * (sobW s ξ * ‖(F : E3 → V) ξ‖ₑ ^ 2) :=
    lintegral_mono fun ξ => by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (ω_pow_le_mul_sobW s ξ) (zero_le _)
  refine h.trans ?_
  rw [two_pow_ennreal, lintegral_const_mul' _ _ (ENNReal.pow_ne_top (by norm_num)),
    eLpNorm_sq, lintegral_μw]

lemma lintegral_ω3_enorm_sq_incl {s : ℕ} (hs : 3 ≤ s) (F : Hm s) :
    ∫⁻ ξ, ω ξ ^ 3 * ‖(F : E3 → V) ξ‖ₑ ^ 2 ≤
      4 * eLpNorm (incl hs F) 2 (μw 3) ^ 2 := by
  have heq : ∫⁻ ξ, ω ξ ^ 3 * ‖(F : E3 → V) ξ‖ₑ ^ 2 =
      ∫⁻ ξ, ω ξ ^ 3 * ‖(incl hs F : E3 → V) ξ‖ₑ ^ 2 := by
    refine lintegral_congr_ae ?_
    filter_upwards [coeFn_incl_vol hs F] with ξ hξ
    simp [hξ]
  rw [heq]
  exact lintegral_ω3_enorm_sq (incl hs F)

/-! ## Convolution on `Ĥ^s`, `s ≥ 3` -/

variable (L : V →L[ℂ] V →L[ℂ] V)

lemma integrable_of_Hm_ge3 {s : ℕ} (hs : 3 ≤ s) (F : Hm s) :
    Integrable (F : E3 → V) volume :=
  integrable_of_Hm (le_trans (by norm_num : 2 ≤ 3) hs) F

lemma integrable_conv_integrand {s : ℕ} (hs : 3 ≤ s) (F G : Hm s) :
    Integrable (fun p : E3 × E3 => L ((F : E3 → V) p.2) ((G : E3 → V) (p.1 - p.2)))
      (volume.prod volume) :=
  (integrable_of_Hm_ge3 hs F).convolution_integrand L (integrable_of_Hm_ge3 hs G)

theorem integrable_conv {s : ℕ} (hs : 3 ≤ s) (F G : Hm s) :
    Integrable ((F : E3 → V) ⋆[L] (G : E3 → V)) volume := by
  simpa only [convolution_def] using (integrable_conv_integrand L hs F G).integral_prod_left

theorem enorm_conv_le {s : ℕ} (F G : Hm s) (ξ : E3) :
    ‖((F : E3 → V) ⋆[L] (G : E3 → V)) ξ‖ₑ ≤
      ‖L‖ₑ * ∫⁻ η, ‖(F : E3 → V) η‖ₑ * ‖(G : E3 → V) (ξ - η)‖ₑ := by
  rw [convolution_def]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← lintegral_const_mul' _ _ (by simp [enorm_ne_top])]
  refine lintegral_mono fun η => ?_
  have h := L.le_opNorm₂ ((F : E3 → V) η) ((G : E3 → V) (ξ - η))
  simp only [← ofReal_norm_eq_enorm]
  have e : ENNReal.ofReal ‖L‖ *
        (ENNReal.ofReal ‖(F : E3 → V) η‖ * ENNReal.ofReal ‖(G : E3 → V) (ξ - η)‖) =
      ENNReal.ofReal (‖L‖ * ‖(F : E3 → V) η‖ * ‖(G : E3 → V) (ξ - η)‖) := by
    rw [← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (norm_nonneg L), mul_assoc]
  rw [e]
  exact ENNReal.ofReal_le_ofReal h

def convN {s : ℕ} (F G : Hm s) (ξ : E3) : ℝ≥0∞ :=
  ∫⁻ η, ‖(F : E3 → V) η‖ₑ * ‖(G : E3 → V) (ξ - η)‖ₑ

lemma measurable_enorm_comp {s : ℕ} (F : Hm s) : Measurable fun ξ => ‖(F : E3 → V) ξ‖ₑ :=
  (Lp.stronglyMeasurable F).measurable.enorm

lemma measurable_convN {s : ℕ} (F G : Hm s) : Measurable (convN F G) :=
  Measurable.lintegral_prod_right'
    (f := fun p : E3 × E3 => ‖(F : E3 → V) p.2‖ₑ * ‖(G : E3 → V) (p.1 - p.2)‖ₑ)
    ((measurable_enorm_comp F).comp measurable_snd |>.mul
      ((measurable_enorm_comp G).comp measurable_sub))

lemma lintegral_ωs_convN_sq {s : ℕ} (F G : Hm s) :
    ∫⁻ ξ, ω ξ ^ s * (convN F G ξ) ^ 2 ≤
      Ks s * Cw * ((∫⁻ x, ω x ^ 3 * ‖(G : E3 → V) x‖ₑ ^ 2) *
          (∫⁻ x, ω x ^ s * ‖(F : E3 → V) x‖ₑ ^ 2) +
        (∫⁻ x, ω x ^ 3 * ‖(F : E3 → V) x‖ₑ ^ 2) *
          (∫⁻ x, ω x ^ s * ‖(G : E3 → V) x‖ₑ ^ 2)) := by
  have e : convN F G = fun ξ => ∫⁻ η, ‖(F : E3 → V) (ξ - η)‖ₑ * ‖(G : E3 → V) η‖ₑ := by
    funext ξ
    unfold convN
    exact (lintegral_sub_left_eq_self
      (fun z => ‖(F : E3 → V) z‖ₑ * ‖(G : E3 → V) (ξ - z)‖ₑ) ξ).symm.trans
      (lintegral_congr fun z => by rw [sub_sub_cancel])
  rw [e]
  exact weighted_conv_tame s (measurable_enorm_comp F) (measurable_enorm_comp G)

/-- Squared `Ĥ^s` energy of the convolution, in tame form. -/
theorem eLpNorm_conv_sq_le {s : ℕ} (hs : 3 ≤ s) (F G : Hm s) :
    eLpNorm ((F : E3 → V) ⋆[L] (G : E3 → V)) 2 (μw s) ^ 2 ≤
      CmSq s * ‖L‖ₑ ^ 2 *
        (eLpNorm (incl hs G) 2 (μw 3) ^ 2 * eLpNorm F 2 (μw s) ^ 2 +
          eLpNorm (incl hs F) 2 (μw 3) ^ 2 * eLpNorm G 2 (μw s) ^ 2) := by
  rw [eLpNorm_sq, lintegral_μw]
  have hpt : ∀ ξ, sobW s ξ * ‖((F : E3 → V) ⋆[L] (G : E3 → V)) ξ‖ₑ ^ 2 ≤
      ENNReal.ofReal (s + 1 : ℝ) * (ω ξ ^ s * (‖L‖ₑ * convN F G ξ) ^ 2) := fun ξ => by
    have h1 : sobW s ξ ≤ ENNReal.ofReal (s + 1 : ℝ) * ω ξ ^ s := sobW_le_mul_ω_pow s ξ
    have h2 : ‖((F : E3 → V) ⋆[L] (G : E3 → V)) ξ‖ₑ ^ 2 ≤ (‖L‖ₑ * convN F G ξ) ^ 2 :=
      pow_le_pow_left₀ (zero_le _) (enorm_conv_le L F G ξ) 2
    calc sobW s ξ * ‖((F : E3 → V) ⋆[L] (G : E3 → V)) ξ‖ₑ ^ 2
        ≤ (ENNReal.ofReal (s + 1 : ℝ) * ω ξ ^ s) *
            ‖((F : E3 → V) ⋆[L] (G : E3 → V)) ξ‖ₑ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (zero_le _)
      _ ≤ (ENNReal.ofReal (s + 1 : ℝ) * ω ξ ^ s) * (‖L‖ₑ * convN F G ξ) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (zero_le _)
      _ = _ := by ring
  have hLtop : ‖L‖ₑ ≠ ⊤ := enorm_ne_top
  have hs1top : ENNReal.ofReal (s + 1 : ℝ) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc ∫⁻ ξ, sobW s ξ * ‖((F : E3 → V) ⋆[L] (G : E3 → V)) ξ‖ₑ ^ 2
      ≤ ∫⁻ ξ, ENNReal.ofReal (s + 1 : ℝ) * (ω ξ ^ s * (‖L‖ₑ * convN F G ξ) ^ 2) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (s + 1 : ℝ) * ‖L‖ₑ ^ 2 * ∫⁻ ξ, ω ξ ^ s * (convN F G ξ) ^ 2 := by
        have hfun : (fun ξ => ω ξ ^ s * (‖L‖ₑ * convN F G ξ) ^ 2) =
            fun ξ => ‖L‖ₑ ^ 2 * (ω ξ ^ s * convN F G ξ ^ 2) := by
          funext ξ; rw [mul_pow]; ring
        rw [lintegral_const_mul' _ _ hs1top, hfun,
          lintegral_const_mul' _ _ (by simp [enorm_ne_top])]
        ring
    _ ≤ ENNReal.ofReal (s + 1 : ℝ) * ‖L‖ₑ ^ 2 *
          (Ks s * Cw * ((∫⁻ x, ω x ^ 3 * ‖(G : E3 → V) x‖ₑ ^ 2) *
              (∫⁻ x, ω x ^ s * ‖(F : E3 → V) x‖ₑ ^ 2) +
            (∫⁻ x, ω x ^ 3 * ‖(F : E3 → V) x‖ₑ ^ 2) *
              (∫⁻ x, ω x ^ s * ‖(G : E3 → V) x‖ₑ ^ 2))) :=
        mul_le_mul_of_nonneg_left (lintegral_ωs_convN_sq F G) (zero_le _)
    _ ≤ ENNReal.ofReal (s + 1 : ℝ) * ‖L‖ₑ ^ 2 *
          (Ks s * Cw * ((4 * eLpNorm (incl hs G) 2 (μw 3) ^ 2) *
              ((2 : ℝ≥0∞) ^ s * eLpNorm F 2 (μw s) ^ 2) +
            (4 * eLpNorm (incl hs F) 2 (μw 3) ^ 2) *
              ((2 : ℝ≥0∞) ^ s * eLpNorm G 2 (μw s) ^ 2))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (zero_le _)) (zero_le _)
        exact add_le_add
          (mul_le_mul (lintegral_ω3_enorm_sq_incl hs G) (lintegral_ωs_enorm_sq s F)
            (zero_le _) (zero_le _))
          (mul_le_mul (lintegral_ω3_enorm_sq_incl hs F) (lintegral_ωs_enorm_sq s G)
            (zero_le _) (zero_le _))
    _ = CmSq s * ‖L‖ₑ ^ 2 *
          (eLpNorm (incl hs G) 2 (μw 3) ^ 2 * eLpNorm F 2 (μw s) ^ 2 +
            eLpNorm (incl hs F) 2 (μw 3) ^ 2 * eLpNorm G 2 (μw s) ^ 2) := by
        set b := eLpNorm F 2 (μw s)
        set c := eLpNorm G 2 (μw s)
        set b3 := eLpNorm (incl hs F) 2 (μw 3)
        set c3 := eLpNorm (incl hs G) 2 (μw 3)
        have hconst : ENNReal.ofReal (s + 1 : ℝ) * Ks s * Cw * 4 * (2 : ℝ≥0∞) ^ s =
            CmSq s := by
          unfold CmSq Ks
          calc ENNReal.ofReal (s + 1 : ℝ) * (2 * (4 : ℝ≥0∞) ^ s) * Cw * 4 * (2 : ℝ≥0∞) ^ s
              = ENNReal.ofReal (s + 1 : ℝ) * Cw *
                  ((2 : ℝ≥0∞) ^ s * (4 : ℝ≥0∞) ^ s * 8) := by ring
            _ = ENNReal.ofReal (s + 1 : ℝ) * Cw * ((8 : ℝ≥0∞) ^ s * 8) := by
                rw [two_mul_four_pow]
            _ = ENNReal.ofReal (s + 1 : ℝ) * (8 : ℝ≥0∞) ^ (s + 1) * Cw := by
                have hpow : (8 : ℝ≥0∞) ^ s * 8 = (8 : ℝ≥0∞) ^ (s + 1) :=
                  (pow_succ (8 : ℝ≥0∞) s).symm
                rw [hpow]; ac_rfl
        calc ENNReal.ofReal (s + 1 : ℝ) * ‖L‖ₑ ^ 2 *
              (Ks s * Cw * ((4 * c3 ^ 2) * ((2 : ℝ≥0∞) ^ s * b ^ 2) +
                (4 * b3 ^ 2) * ((2 : ℝ≥0∞) ^ s * c ^ 2)))
            = (ENNReal.ofReal (s + 1 : ℝ) * Ks s * Cw * 4 * (2 : ℝ≥0∞) ^ s) * ‖L‖ₑ ^ 2 *
                (c3 ^ 2 * b ^ 2 + b3 ^ 2 * c ^ 2) := by ring
          _ = CmSq s * ‖L‖ₑ ^ 2 * (c3 ^ 2 * b ^ 2 + b3 ^ 2 * c ^ 2) := by rw [hconst]

lemma memLp_conv {s : ℕ} (hs : 3 ≤ s) (F G : Hm s) :
    MemLp ((F : E3 → V) ⋆[L] (G : E3 → V)) 2 (μw s) := by
  refine ⟨(integrable_conv L hs F G).aestronglyMeasurable.mono_ac (ac_μw s), ?_⟩
  have h := eLpNorm_conv_sq_le L hs F G
  refine lt_of_le_of_ne le_top fun htop => ?_
  rw [htop] at h
  have : (⊤ : ℝ≥0∞) ≤ _ := h
  refine (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (CmSq_lt_top s) (ENNReal.pow_lt_top enorm_ne_top.lt_top))
      (ENNReal.add_lt_top.2
        ⟨ENNReal.mul_lt_top (ENNReal.pow_lt_top (Lp.eLpNorm_lt_top (incl hs G)))
            (ENNReal.pow_lt_top (Lp.eLpNorm_lt_top F)),
          ENNReal.mul_lt_top (ENNReal.pow_lt_top (Lp.eLpNorm_lt_top (incl hs F)))
            (ENNReal.pow_lt_top (Lp.eLpNorm_lt_top G))⟩)).ne
    (top_le_iff.1 this)

/-- Convolution as an `Ĥ^s` element. -/
def mulF {s : ℕ} (hs : 3 ≤ s) (F G : Hm s) : Hm s := (memLp_conv L hs F G).toLp _

lemma coeFn_mulF {s : ℕ} (hs : 3 ≤ s) (F G : Hm s) :
    (mulF L hs F G : E3 → V) =ᵐ[μw s] ((F : E3 → V) ⋆[L] (G : E3 → V)) :=
  MemLp.coeFn_toLp (memLp_conv L hs F G)

/-- **Tame `Ĥ^s` product estimate**:
`‖F ⋆[L] G‖_{Ĥ^s} ≤ C_s ‖L‖ (‖F‖_{Ĥ^s} ‖G‖_{Ĥ³} + ‖F‖_{Ĥ³} ‖G‖_{Ĥ^s})`. -/
theorem norm_mulF_le {s : ℕ} (hs : 3 ≤ s) (F G : Hm s) :
    ‖mulF L hs F G‖ ≤
      Cm s * ‖L‖ * (‖F‖ * ‖incl hs G‖ + ‖incl hs F‖ * ‖G‖) := by
  have hx := eLpNorm_conv_sq_le L hs F G
  rw [eLpNorm_congr_ae (coeFn_mulF L hs F G).symm] at hx
  rw [Lp.norm_def, Lp.norm_def, Lp.norm_def, Lp.norm_def, Lp.norm_def]
  set a := eLpNorm (mulF L hs F G) 2 (μw s)
  set b := eLpNorm F 2 (μw s)
  set c := eLpNorm G 2 (μw s)
  set b3 := eLpNorm (incl hs F) 2 (μw 3)
  set c3 := eLpNorm (incl hs G) 2 (μw 3)
  have hb := Lp.eLpNorm_ne_top F
  have hc := Lp.eLpNorm_ne_top G
  have hb3 := Lp.eLpNorm_ne_top (incl hs F)
  have hc3 := Lp.eLpNorm_ne_top (incl hs G)
  have hL0 : 0 ≤ ‖L‖ := ContinuousLinearMap.opNorm_nonneg L
  have hfin : CmSq s * ‖L‖ₑ ^ 2 * (c3 ^ 2 * b ^ 2 + b3 ^ 2 * c ^ 2) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (CmSq_ne_top s) (ENNReal.pow_ne_top enorm_ne_top))
      (ENNReal.add_ne_top.2
        ⟨ENNReal.mul_ne_top (ENNReal.pow_ne_top hc3) (ENNReal.pow_ne_top hb),
          ENNReal.mul_ne_top (ENNReal.pow_ne_top hb3) (ENNReal.pow_ne_top hc)⟩)
  have h' : a.toReal ^ 2 ≤
      (CmSq s).toReal * ‖L‖ ^ 2 * (c3.toReal ^ 2 * b.toReal ^ 2 + b3.toReal ^ 2 * c.toReal ^ 2) := by
    have hrt := ENNReal.toReal_mono hfin hx
    rw [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_add
        (ENNReal.mul_ne_top (ENNReal.pow_ne_top hc3) (ENNReal.pow_ne_top hb))
        (ENNReal.mul_ne_top (ENNReal.pow_ne_top hb3) (ENNReal.pow_ne_top hc)),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow,
      ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_pow] at hrt
    rwa [← ofReal_norm_eq_enorm L, ENNReal.toReal_ofReal hL0] at hrt
  have hsqrt := Real.sqrt_le_sqrt h'
  rw [Real.sqrt_sq ENNReal.toReal_nonneg] at hsqrt
  refine hsqrt.trans ?_
  have hK : 0 ≤ (CmSq s).toReal := ENNReal.toReal_nonneg
  have hb0 : 0 ≤ b.toReal := ENNReal.toReal_nonneg
  have hc0 : 0 ≤ c.toReal := ENNReal.toReal_nonneg
  have hb30 : 0 ≤ b3.toReal := ENNReal.toReal_nonneg
  have hc30 : 0 ≤ c3.toReal := ENNReal.toReal_nonneg
  have hre : (CmSq s).toReal * ‖L‖ ^ 2 *
        (c3.toReal ^ 2 * b.toReal ^ 2 + b3.toReal ^ 2 * c.toReal ^ 2) =
      (CmSq s).toReal * (‖L‖ ^ 2 *
        (c3.toReal ^ 2 * b.toReal ^ 2 + b3.toReal ^ 2 * c.toReal ^ 2)) := by ring
  rw [hre, Real.sqrt_mul hK, Real.sqrt_mul (sq_nonneg _), Cm_eq_sqrt s, Real.sqrt_sq hL0]
  have hsum : Real.sqrt (c3.toReal ^ 2 * b.toReal ^ 2 + b3.toReal ^ 2 * c.toReal ^ 2) ≤
      b.toReal * c3.toReal + b3.toReal * c.toReal := by
    have hab : 0 ≤ b.toReal * c3.toReal := mul_nonneg hb0 hc30
    have hcd : 0 ≤ b3.toReal * c.toReal := mul_nonneg hb30 hc0
    have hineq : c3.toReal ^ 2 * b.toReal ^ 2 + b3.toReal ^ 2 * c.toReal ^ 2 ≤
        (b.toReal * c3.toReal + b3.toReal * c.toReal) ^ 2 := by
      calc c3.toReal ^ 2 * b.toReal ^ 2 + b3.toReal ^ 2 * c.toReal ^ 2
          = (b.toReal * c3.toReal) ^ 2 + (b3.toReal * c.toReal) ^ 2 := by ring
        _ ≤ (b.toReal * c3.toReal + b3.toReal * c.toReal) ^ 2 := by nlinarith [mul_nonneg hab hcd]
    have hnn : 0 ≤ b.toReal * c3.toReal + b3.toReal * c.toReal := add_nonneg hab hcd
    calc Real.sqrt (c3.toReal ^ 2 * b.toReal ^ 2 + b3.toReal ^ 2 * c.toReal ^ 2)
        ≤ Real.sqrt ((b.toReal * c3.toReal + b3.toReal * c.toReal) ^ 2) :=
          Real.sqrt_le_sqrt hineq
      _ = b.toReal * c3.toReal + b3.toReal * c.toReal := Real.sqrt_sq hnn
  calc Cm s * (‖L‖ * Real.sqrt (c3.toReal ^ 2 * b.toReal ^ 2 + b3.toReal ^ 2 * c.toReal ^ 2))
      ≤ Cm s * (‖L‖ * (b.toReal * c3.toReal + b3.toReal * c.toReal)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hL0) (Cm_nonneg s)
    _ = Cm s * ‖L‖ * (b.toReal * c3.toReal + b3.toReal * c.toReal) := by ring

#print axioms ProductHm.ω_le_four_max
#print axioms ProductHm.vs_le
#print axioms ProductHm.weighted_conv_le_pow
#print axioms ProductHm.weighted_conv_tame
#print axioms ProductHm.lintegral_ωs_enorm_sq
#print axioms ProductHm.lintegral_ω3_enorm_sq_incl
#print axioms ProductHm.integrable_conv
#print axioms ProductHm.eLpNorm_conv_sq_le
#print axioms ProductHm.memLp_conv
#print axioms ProductHm.norm_mulF_le

end ProductHm
