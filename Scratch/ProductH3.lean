import Scratch.ProductEstimate
import Mathlib.Analysis.Convolution

/-! # Bilinear product on `Ĥ³` (Fourier-side convolution)

For any continuous bilinear `L : V →L[ℂ] V →L[ℂ] V`, the convolution
`(F ⋆[L] G)(ξ) = ∫ L(F η)(G(ξ-η)) dη` lands in `Ĥ³` and satisfies
`‖F ⋆[L] G‖_{Ĥ³} ≤ C_⋆ ‖L‖ ‖F‖_{Ĥ³} ‖G‖_{Ĥ³}`. -/

open MeasureTheory Real Filter Topology
open scoped ENNReal Convolution

noncomputable section
namespace ProductH3

open LerayHeat SobolevFourier SobolevHilbert ProductEstimate

/-- `C⋆² = 4096 C_w` (from `256 C_w` and `ω³ ≤ 4 sobW 3` twice). -/
def CstarSq : ℝ≥0∞ := 4096 * Cw

lemma CstarSq_lt_top : CstarSq < ⊤ :=
  ENNReal.mul_lt_top (by norm_num) Cw_lt_top

lemma CstarSq_ne_top : CstarSq ≠ ⊤ := CstarSq_lt_top.ne

/-- Real square-root constant `C⋆ = 64 √C_w`. -/
def Cstar : ℝ := Real.sqrt (4096 * Cw.toReal)

lemma Cstar_nonneg : 0 ≤ Cstar := Real.sqrt_nonneg _

lemma lintegral_ω3_enorm_sq (F : Hm 3) :
    ∫⁻ ξ, ω ξ ^ 3 * ‖(F : E3 → V) ξ‖ₑ ^ 2 ≤ 4 * eLpNorm F 2 (μw 3) ^ 2 := by
  have h : ∫⁻ ξ, ω ξ ^ 3 * ‖(F : E3 → V) ξ‖ₑ ^ 2 ≤ ∫⁻ ξ, 4 * (sobW 3 ξ * ‖(F : E3 → V) ξ‖ₑ ^ 2) :=
    lintegral_mono fun ξ => by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (sobW3_le_ω3 ξ).2 (zero_le _)
  refine h.trans ?_
  rw [lintegral_const_mul' _ _ (by norm_num), eLpNorm_sq, lintegral_μw]

lemma lintegral_enorm_sq_le (F : Hm 3) :
    (∫⁻ ξ, ‖(F : E3 → V) ξ‖ₑ) ^ 2 ≤ 4 * Cw * eLpNorm F 2 (μw 3) ^ 2 := by
  have hF : Measurable fun ξ => ‖(F : E3 → V) ξ‖ₑ :=
    (Lp.stronglyMeasurable F).measurable.enorm
  calc (∫⁻ ξ, ‖(F : E3 → V) ξ‖ₑ) ^ 2
      ≤ Cw * ∫⁻ ξ, ω ξ ^ 3 * ‖(F : E3 → V) ξ‖ₑ ^ 2 := lintegral_sq_le hF
    _ ≤ Cw * (4 * eLpNorm F 2 (μw 3) ^ 2) := mul_le_mul_right (lintegral_ω3_enorm_sq F) _
    _ = 4 * Cw * eLpNorm F 2 (μw 3) ^ 2 := by ring

/-- `Ĥ³` functions are integrable with respect to Lebesgue measure. -/
theorem integrable_of_H3 (F : Hm 3) : Integrable (F : E3 → V) volume := by
  have hsm : AEStronglyMeasurable (F : E3 → V) volume :=
    (Lp.stronglyMeasurable F).aestronglyMeasurable.mono_ac (ac_vol 3)
  have hL1 := lintegral_enorm_sq_le F
  have hfin : ∫⁻ ξ, ‖(F : E3 → V) ξ‖ₑ < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => ?_
    have : (⊤ : ℝ≥0∞) ^ 2 ≤ 4 * Cw * eLpNorm F 2 (μw 3) ^ 2 := by simpa [htop] using hL1
    exact (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) Cw_lt_top)
      (ENNReal.pow_lt_top (Lp.eLpNorm_lt_top F))).ne (top_le_iff.1 this)
  exact ⟨hsm, hfin⟩

variable (L : V →L[ℂ] V →L[ℂ] V)

lemma integrable_conv_integrand (F G : Hm 3) :
    Integrable (fun p : E3 × E3 => L ((F : E3 → V) p.2) ((G : E3 → V) (p.1 - p.2)))
      (volume.prod volume) :=
  (integrable_of_H3 F).convolution_integrand L (integrable_of_H3 G)

/-- The bilinear convolution is integrable (hence a.e. strongly measurable). -/
theorem integrable_conv (F G : Hm 3) :
    Integrable ((F : E3 → V) ⋆[L] (G : E3 → V)) volume := by
  simpa only [convolution_def] using (integrable_conv_integrand L F G).integral_prod_left

/-- Pointwise bound `‖(F ⋆[L] G) ξ‖ₑ ≤ ‖L‖ₑ * ∫⁻ ‖F η‖ₑ * ‖G(ξ-η)‖ₑ`. -/
theorem enorm_conv_le (F G : Hm 3) (ξ : E3) :
    ‖((F : E3 → V) ⋆[L] (G : E3 → V)) ξ‖ₑ ≤
      ‖L‖ₑ * ∫⁻ η, ‖(F : E3 → V) η‖ₑ * ‖(G : E3 → V) (ξ - η)‖ₑ := by
  rw [convolution_def]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← lintegral_const_mul' _ _ (by simp [enorm_ne_top])]
  refine lintegral_mono fun η => ?_
  have h := L.le_opNorm₂ ((F : E3 → V) η) ((G : E3 → V) (ξ - η))
  simp only [← ofReal_norm_eq_enorm]
  have e : ENNReal.ofReal ‖L‖ * (ENNReal.ofReal ‖(F : E3 → V) η‖ * ENNReal.ofReal ‖(G : E3 → V) (ξ - η)‖) =
      ENNReal.ofReal (‖L‖ * ‖(F : E3 → V) η‖ * ‖(G : E3 → V) (ξ - η)‖) := by
    rw [← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (norm_nonneg L), mul_assoc]
  rw [e]
  exact ENNReal.ofReal_le_ofReal h

/-- The convolution of the pointwise norms, as an `ℝ≥0∞`-function. -/
def convN (F G : Hm 3) (ξ : E3) : ℝ≥0∞ :=
  ∫⁻ η, ‖(F : E3 → V) η‖ₑ * ‖(G : E3 → V) (ξ - η)‖ₑ

lemma measurable_enorm_comp (F : Hm 3) : Measurable fun ξ => ‖(F : E3 → V) ξ‖ₑ :=
  (Lp.stronglyMeasurable F).measurable.enorm

lemma measurable_convN (F G : Hm 3) : Measurable (convN F G) :=
  Measurable.lintegral_prod_right'
    (f := fun p : E3 × E3 => ‖(F : E3 → V) p.2‖ₑ * ‖(G : E3 → V) (p.1 - p.2)‖ₑ)
    ((measurable_enorm_comp F).comp measurable_snd |>.mul
      ((measurable_enorm_comp G).comp measurable_sub))

lemma lintegral_ω3_convN_sq (F G : Hm 3) :
    ∫⁻ ξ, ω ξ ^ 3 * (convN F G ξ) ^ 2 ≤
      256 * Cw * ((∫⁻ x, ω x ^ 3 * ‖(F : E3 → V) x‖ₑ ^ 2) *
        ∫⁻ x, ω x ^ 3 * ‖(G : E3 → V) x‖ₑ ^ 2) := by
  -- `weighted_conv_le_H3` uses ∫ F(ξ-η)*G(η), which equals convN after the substitution
  -- η ↦ ξ-η (translation invariance of Lebesgue measure).
  have e : convN F G = fun ξ => ∫⁻ η, ‖(F : E3 → V) (ξ - η)‖ₑ * ‖(G : E3 → V) η‖ₑ := by
    funext ξ
    unfold convN
    exact (lintegral_sub_left_eq_self
      (fun z => ‖(F : E3 → V) z‖ₑ * ‖(G : E3 → V) (ξ - z)‖ₑ) ξ).symm.trans
      (lintegral_congr fun z => by rw [sub_sub_cancel])
  rw [e]
  exact weighted_conv_le_H3 (measurable_enorm_comp F) (measurable_enorm_comp G)

/-- Squared `Ĥ³` energy of the convolution. -/
theorem eLpNorm_conv_sq_le (F G : Hm 3) :
    eLpNorm ((F : E3 → V) ⋆[L] (G : E3 → V)) 2 (μw 3) ^ 2 ≤
      CstarSq * ‖L‖ₑ ^ 2 * (eLpNorm F 2 (μw 3) ^ 2 * eLpNorm G 2 (μw 3) ^ 2) := by
  rw [eLpNorm_sq, lintegral_μw]
  have hpt : ∀ ξ, sobW 3 ξ * ‖((F : E3 → V) ⋆[L] (G : E3 → V)) ξ‖ₑ ^ 2 ≤
      ω ξ ^ 3 * (‖L‖ₑ * convN F G ξ) ^ 2 := fun ξ => by
    refine mul_le_mul (sobW3_le_ω3 ξ).1 ?_ (zero_le _) (zero_le _)
    exact pow_le_pow_left₀ (zero_le _) (enorm_conv_le L F G ξ) 2
  calc ∫⁻ ξ, sobW 3 ξ * ‖((F : E3 → V) ⋆[L] (G : E3 → V)) ξ‖ₑ ^ 2
      ≤ ∫⁻ ξ, ω ξ ^ 3 * (‖L‖ₑ * convN F G ξ) ^ 2 := lintegral_mono hpt
    _ = ‖L‖ₑ ^ 2 * ∫⁻ ξ, ω ξ ^ 3 * (convN F G ξ) ^ 2 := by
        simp only [mul_pow]
        rw [← lintegral_const_mul' _ _ (by simp [enorm_ne_top])]
        congr 1; funext ξ; ring
    _ ≤ ‖L‖ₑ ^ 2 * (256 * Cw * ((∫⁻ x, ω x ^ 3 * ‖(F : E3 → V) x‖ₑ ^ 2) *
          ∫⁻ x, ω x ^ 3 * ‖(G : E3 → V) x‖ₑ ^ 2)) :=
        mul_le_mul_right (lintegral_ω3_convN_sq F G) _
    _ ≤ ‖L‖ₑ ^ 2 * (256 * Cw * ((4 * eLpNorm F 2 (μw 3) ^ 2) *
          (4 * eLpNorm G 2 (μw 3) ^ 2))) := by
        refine mul_le_mul_right (mul_le_mul_right (mul_le_mul (lintegral_ω3_enorm_sq F)
          (lintegral_ω3_enorm_sq G) (zero_le _) (zero_le _)) _) _
    _ = CstarSq * ‖L‖ₑ ^ 2 * (eLpNorm F 2 (μw 3) ^ 2 * eLpNorm G 2 (μw 3) ^ 2) := by
        unfold CstarSq; ring

lemma memLp_conv (F G : Hm 3) : MemLp ((F : E3 → V) ⋆[L] (G : E3 → V)) 2 (μw 3) := by
  refine ⟨(integrable_conv L F G).aestronglyMeasurable.mono_ac (ac_μw 3), ?_⟩
  have h := eLpNorm_conv_sq_le L F G
  refine lt_of_le_of_ne le_top fun htop => ?_
  rw [htop] at h
  have : (⊤ : ℝ≥0∞) ≤ _ := h
  refine (ENNReal.mul_lt_top (ENNReal.mul_lt_top CstarSq_lt_top (ENNReal.pow_lt_top enorm_ne_top.lt_top))
    (ENNReal.mul_lt_top (ENNReal.pow_lt_top (Lp.eLpNorm_lt_top F))
      (ENNReal.pow_lt_top (Lp.eLpNorm_lt_top G)))).ne (top_le_iff.1 this)

/-- Convolution as an `Ĥ³` element. -/
def mulF (F G : Hm 3) : Hm 3 := (memLp_conv L F G).toLp _

lemma coeFn_mulF (F G : Hm 3) :
    (mulF L F G : E3 → V) =ᵐ[μw 3] ((F : E3 → V) ⋆[L] (G : E3 → V)) :=
  MemLp.coeFn_toLp (memLp_conv L F G)

/-- **`Ĥ³` product estimate**: `‖F ⋆[L] G‖ ≤ C⋆ ‖L‖ ‖F‖ ‖G‖`. -/
theorem norm_mulF_le (F G : Hm 3) : ‖mulF L F G‖ ≤ Cstar * ‖L‖ * ‖F‖ * ‖G‖ := by
  have hx := eLpNorm_conv_sq_le L F G
  rw [eLpNorm_congr_ae (coeFn_mulF L F G).symm] at hx
  rw [Lp.norm_def, Lp.norm_def, Lp.norm_def]
  set a := eLpNorm (mulF L F G) 2 (μw 3)
  set b := eLpNorm F 2 (μw 3)
  set c := eLpNorm G 2 (μw 3)
  have hb := Lp.eLpNorm_ne_top F
  have hc := Lp.eLpNorm_ne_top G
  have hL0 : 0 ≤ ‖L‖ := ContinuousLinearMap.opNorm_nonneg L
  have hfin : CstarSq * ‖L‖ₑ ^ 2 * (b ^ 2 * c ^ 2) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top CstarSq_ne_top (ENNReal.pow_ne_top enorm_ne_top))
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top hb) (ENNReal.pow_ne_top hc))
  have h' : a.toReal ^ 2 ≤ CstarSq.toReal * ‖L‖ ^ 2 * (b.toReal ^ 2 * c.toReal ^ 2) := by
    have hrt := ENNReal.toReal_mono hfin hx
    rw [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_pow] at hrt
    rwa [← ofReal_norm_eq_enorm L, ENNReal.toReal_ofReal hL0] at hrt
  have hsqrt := Real.sqrt_le_sqrt h'
  rw [Real.sqrt_sq ENNReal.toReal_nonneg] at hsqrt
  refine hsqrt.trans ?_
  have hK : 0 ≤ CstarSq.toReal := ENNReal.toReal_nonneg
  have hb0 : 0 ≤ b.toReal := ENNReal.toReal_nonneg
  have hc0 : 0 ≤ c.toReal := ENNReal.toReal_nonneg
  have hre : CstarSq.toReal * ‖L‖ ^ 2 * (b.toReal ^ 2 * c.toReal ^ 2) =
      CstarSq.toReal * (‖L‖ ^ 2 * (b.toReal ^ 2 * c.toReal ^ 2)) := by ring
  rw [hre, Real.sqrt_mul hK, Real.sqrt_mul (sq_nonneg _), Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq hL0, Real.sqrt_sq hb0, Real.sqrt_sq hc0]
  have hC : Real.sqrt CstarSq.toReal = Cstar := by
    unfold Cstar CstarSq
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4096)]
  rw [hC]
  nlinarith [hL0, hb0, hc0, Cstar_nonneg]

end ProductH3

#print axioms ProductH3.integrable_of_H3
#print axioms ProductH3.integrable_conv
#print axioms ProductH3.enorm_conv_le
#print axioms ProductH3.eLpNorm_conv_sq_le
#print axioms ProductH3.memLp_conv
#print axioms ProductH3.norm_mulF_le
