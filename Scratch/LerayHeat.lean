import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Leray projector and heat semigroup on `L²(ℝ³; ℂ³)` (Fourier side, Plancherel)

Pointwise Fourier multipliers `ξ ↦ T ξ` with `‖T ξ‖ ≤ 1` act on `L²` with norm `≤ 1`;
conjugating by Mathlib's `L²` Fourier isometry gives
* the **Leray projector** `ℙ = 𝓕⁻ ∘ (Π_ξ) ∘ 𝓕`, `Π_ξ` = orthogonal projection onto `ξ^⊥`;
* the **heat semigroup** `e^{τΔ} = 𝓕⁻ ∘ (e^{-4π²τ|ξ|²}) ∘ 𝓕`, `τ = ν t ≥ 0`. -/

open MeasureTheory FourierTransform
open scoped ENNReal ComplexInnerProductSpace

noncomputable section
namespace LerayHeat

abbrev E3 := EuclideanSpace ℝ (Fin 3)
abbrev V := EuclideanSpace ℂ (Fin 3)
/-- `L²(ℝ³; ℂ³)`. -/
abbrev L2V := Lp (α := E3) V 2

/-! ## Pointwise multipliers on `L²` -/

section PMul
variable (T : E3 → V →L[ℂ] V)
  (hT : ∀ g : E3 → V, AEStronglyMeasurable g → AEStronglyMeasurable (fun ξ => T ξ (g ξ)))
  (hb : ∀ ξ, ‖T ξ‖ ≤ 1)

include hT hb in
lemma memLp_pmul (f : L2V) : MemLp (fun ξ => T ξ (f ξ)) 2 :=
  MemLp.of_le (Lp.memLp f) (hT _ (Lp.aestronglyMeasurable f))
    (Filter.Eventually.of_forall fun ξ =>
      ((T ξ).le_opNorm _).trans (by simpa using mul_le_mul_of_nonneg_right (hb ξ) (norm_nonneg _)))

/-- Underlying map. -/
def pmulFun (f : L2V) : L2V := (memLp_pmul T hT hb f).toLp _

lemma coeFn_pmulFun (f : L2V) : (pmulFun T hT hb f : E3 → V) =ᵐ[volume] fun ξ => T ξ (f ξ) :=
  MemLp.coeFn_toLp (memLp_pmul T hT hb f)

lemma pmulFun_add (f g : L2V) : pmulFun T hT hb (f + g) = pmulFun T hT hb f + pmulFun T hT hb g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_pmulFun T hT hb (f + g), Lp.coeFn_add f g,
    Lp.coeFn_add (pmulFun T hT hb f) (pmulFun T hT hb g), coeFn_pmulFun T hT hb f,
    coeFn_pmulFun T hT hb g] with ξ h1 h2 h3 h4 h5
  rw [h1, h3, Pi.add_apply, h4, h5, h2, Pi.add_apply, map_add]

lemma pmulFun_smul (c : ℂ) (f : L2V) : pmulFun T hT hb (c • f) = c • pmulFun T hT hb f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_pmulFun T hT hb (c • f), Lp.coeFn_smul c f,
    Lp.coeFn_smul c (pmulFun T hT hb f), coeFn_pmulFun T hT hb f] with ξ h1 h2 h3 h4
  rw [h1, h3, Pi.smul_apply, h4, h2, Pi.smul_apply, map_smul]

lemma norm_pmulFun_le (f : L2V) : ‖pmulFun T hT hb f‖ ≤ 1 * ‖f‖ := by
  rw [one_mul]
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [coeFn_pmulFun T hT hb f] with ξ h
  rw [h]
  exact ((T ξ).le_opNorm _).trans (by
    simpa using mul_le_mul_of_nonneg_right (hb ξ) (norm_nonneg _))

/-- Multiplication operator `f ↦ (ξ ↦ T ξ (f ξ))` on `L²`, norm `≤ 1`. -/
def pmul : L2V →L[ℂ] L2V :=
  LinearMap.mkContinuous ⟨⟨pmulFun T hT hb, pmulFun_add T hT hb⟩, pmulFun_smul T hT hb⟩ 1
    (norm_pmulFun_le T hT hb)

lemma pmul_apply (f : L2V) : pmul T hT hb f = pmulFun T hT hb f := rfl

lemma coeFn_pmul (f : L2V) : (pmul T hT hb f : E3 → V) =ᵐ[volume] fun ξ => T ξ (f ξ) :=
  coeFn_pmulFun T hT hb f

lemma norm_pmul_le (f : L2V) : ‖pmul T hT hb f‖ ≤ ‖f‖ := by
  simpa using norm_pmulFun_le T hT hb f

lemma pmul_eq_of_ae {f g : L2V} (h : ∀ᵐ ξ, T ξ (f ξ) = g ξ) : pmul T hT hb f = g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_pmul T hT hb f, h] with ξ h1 h2
  rw [h1, h2]

/-- Self-adjoint symbols give self-adjoint multipliers. -/
lemma inner_pmul (hs : ∀ ξ v w, ⟪T ξ v, w⟫ = ⟪v, T ξ w⟫) (f g : L2V) :
    ⟪pmul T hT hb f, g⟫ = ⟪f, pmul T hT hb g⟫ := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_pmul T hT hb f, coeFn_pmul T hT hb g] with ξ h1 h2
  rw [h1, h2, hs]

end PMul

/-- Composition of multipliers is the multiplier of the pointwise composition. -/
lemma pmul_pmul (T₁ T₂ T₃ : E3 → V →L[ℂ] V)
    (hT₁ : ∀ g : E3 → V, AEStronglyMeasurable g → AEStronglyMeasurable (fun ξ => T₁ ξ (g ξ)))
    (hb₁ : ∀ ξ, ‖T₁ ξ‖ ≤ 1)
    (hT₂ : ∀ g : E3 → V, AEStronglyMeasurable g → AEStronglyMeasurable (fun ξ => T₂ ξ (g ξ)))
    (hb₂ : ∀ ξ, ‖T₂ ξ‖ ≤ 1)
    (hT₃ : ∀ g : E3 → V, AEStronglyMeasurable g → AEStronglyMeasurable (fun ξ => T₃ ξ (g ξ)))
    (hb₃ : ∀ ξ, ‖T₃ ξ‖ ≤ 1) (h : ∀ ξ v, T₁ ξ (T₂ ξ v) = T₃ ξ v) (f : L2V) :
    pmul T₁ hT₁ hb₁ (pmul T₂ hT₂ hb₂ f) = pmul T₃ hT₃ hb₃ f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_pmul T₁ hT₁ hb₁ (pmul T₂ hT₂ hb₂ f), coeFn_pmul T₂ hT₂ hb₂ f,
    coeFn_pmul T₃ hT₃ hb₃ f] with ξ h1 h2 h3
  rw [h1, h2, h3, h]

/-! ## Leray symbol: orthogonal projection onto `ξ^⊥` -/

/-- Complexification `ξ ↦ ξ ∈ ℂ³`. -/
def ξc (ξ : E3) : V := WithLp.toLp 2 (fun i => (ξ i : ℂ))

lemma continuous_ξc : Continuous ξc := by
  unfold ξc
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  exact Complex.continuous_ofReal.comp ((PiLp.continuous_apply 2 _ i))

/-- `Π_ξ`: orthogonal projection onto `(ℂ ξ)^⊥`. -/
def lerSym (ξ : E3) : V →L[ℂ] V := (ℂ ∙ ξc ξ)ᗮ.starProjection

lemma lerSym_apply (ξ : E3) (v : V) :
    lerSym ξ v = v - (⟪ξc ξ, v⟫ / ((‖ξc ξ‖ ^ 2 : ℝ) : ℂ)) • ξc ξ := by
  rw [lerSym, Submodule.starProjection_orthogonal_val, Submodule.starProjection_singleton]
  rfl

lemma lerSym_meas (g : E3 → V) (hg : AEStronglyMeasurable g) :
    AEStronglyMeasurable (fun ξ => lerSym ξ (g ξ)) := by
  simp only [lerSym_apply]
  have hc := continuous_ξc
  have hn : Measurable (fun ξ : E3 => (((‖ξc ξ‖ ^ 2 : ℝ)) : ℂ)) :=
    (Complex.continuous_ofReal.comp (hc.norm.pow 2)).measurable
  have hi : AEStronglyMeasurable (fun ξ => ⟪ξc ξ, g ξ⟫) := hc.aestronglyMeasurable.inner hg
  have hd : AEStronglyMeasurable (fun ξ => ⟪ξc ξ, g ξ⟫ / ((‖ξc ξ‖ ^ 2 : ℝ) : ℂ)) :=
    (hi.aemeasurable.div hn.aemeasurable).aestronglyMeasurable
  exact hg.sub (hd.smul hc.aestronglyMeasurable)

lemma lerSym_norm (ξ : E3) : ‖lerSym ξ‖ ≤ 1 := Submodule.starProjection_norm_le _

lemma lerSym_idem (ξ : E3) (v : V) : lerSym ξ (lerSym ξ v) = lerSym ξ v := by
  unfold lerSym
  exact Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ v)

lemma lerSym_selfAdj (ξ : E3) (v w : V) : ⟪lerSym ξ v, w⟫ = ⟪v, lerSym ξ w⟫ :=
  Submodule.inner_starProjection_left_eq_right _ v w

lemma lerSym_perp (ξ : E3) (v : V) : ⟪ξc ξ, lerSym ξ v⟫ = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.1 (Submodule.starProjection_apply_mem _ v)

lemma lerSym_fix {ξ : E3} {v : V} (h : ⟪ξc ξ, v⟫ = 0) : lerSym ξ v = v :=
  Submodule.starProjection_eq_self_iff.2 (Submodule.mem_orthogonal_singleton_iff_inner_right.2 h)

set_option backward.isDefEq.respectTransparency false in
lemma lerSym_grad (ξ : E3) (c : ℂ) : lerSym ξ (c • ξc ξ) = 0 := by
  rw [lerSym_apply, inner_smul_right]
  by_cases h : ξc ξ = 0
  · simp [h]
  · have hn : (‖ξc ξ‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 h).ne'
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rw [← sub_smul]
    convert zero_smul ℂ (ξc ξ) using 2
    field_simp
    simp



/-! ## The Leray projector on `L²(ℝ³; ℂ³)` -/

/-- Fourier-side Leray multiplier. -/
def lerayF : L2V →L[ℂ] L2V := pmul lerSym lerSym_meas lerSym_norm

/-- **Leray projector** `ℙ = 𝓕⁻ Π_ξ 𝓕`. -/
def leray (f : L2V) : L2V := 𝓕⁻ (lerayF (𝓕 f))

lemma fourier_leray (f : L2V) : 𝓕 (leray f) = lerayF (𝓕 f) := by
  rw [leray, fourier_fourierInv_eq]

lemma norm_fourierInv (g : L2V) : ‖𝓕⁻ g‖ = ‖g‖ :=
  (Lp.fourierTransformₗᵢ E3 V).symm.norm_map g

lemma leray_add (f g : L2V) : leray (f + g) = leray f + leray g := by
  simp only [leray, FourierAdd.fourier_add, map_add, FourierInvAdd.fourierInv_add]

lemma leray_smul (c : ℂ) (f : L2V) : leray (c • f) = c • leray f := by
  simp only [leray, FourierSMul.fourier_smul, map_smul, FourierInvSMul.fourierInv_smul]

/-- `‖ℙ f‖₂ ≤ ‖f‖₂`. -/
theorem norm_leray_le (f : L2V) : ‖leray f‖ ≤ ‖f‖ := by
  rw [leray, norm_fourierInv]
  exact (norm_pmul_le _ _ _ _).trans (le_of_eq (Lp.norm_fourier_eq f))

/-- `ℙ² = ℙ`. -/
theorem leray_leray (f : L2V) : leray (leray f) = leray f := by
  rw [leray, fourier_leray]
  unfold lerayF
  rw [pmul_pmul lerSym lerSym lerSym lerSym_meas lerSym_norm lerSym_meas lerSym_norm lerSym_meas
      lerSym_norm lerSym_idem]
  rfl

/-- `ℙ` is self-adjoint. -/
theorem inner_leray (f g : L2V) : ⟪leray f, g⟫ = ⟪f, leray g⟫ := by
  have h1 : ⟪leray f, g⟫ = ⟪𝓕 (leray f), 𝓕 g⟫ := (Lp.inner_fourier_eq _ _).symm
  have h2 : ⟪f, leray g⟫ = ⟪𝓕 f, 𝓕 (leray g)⟫ := (Lp.inner_fourier_eq _ _).symm
  rw [h1, h2, fourier_leray, fourier_leray]
  unfold lerayF
  exact inner_pmul _ _ _ lerSym_selfAdj _ _

/-- `ℙ f` is divergence-free (Fourier side: `ξ · 𝓕(ℙ f)(ξ) = 0` a.e.). -/
theorem leray_divFree (f : L2V) : ∀ᵐ ξ, ⟪ξc ξ, ((𝓕 (leray f) : L2V) : E3 → V) ξ⟫ = 0 := by
  rw [fourier_leray]
  unfold lerayF
  filter_upwards [coeFn_pmul lerSym lerSym_meas lerSym_norm (𝓕 f)] with ξ h
  rw [h]; exact lerSym_perp ξ _

/-- `ℙ` fixes divergence-free fields. -/
theorem leray_eq_self {f : L2V} (h : ∀ᵐ ξ, ⟪ξc ξ, ((𝓕 f : L2V) : E3 → V) ξ⟫ = 0) : leray f = f := by
  have : lerayF (𝓕 f) = 𝓕 f :=
    pmul_eq_of_ae _ _ _ (by filter_upwards [h] with ξ hξ; exact lerSym_fix hξ)
  rw [leray, this, fourierInv_fourier_eq]

/-- `ℙ` annihilates gradients (Fourier side: `𝓕 f (ξ) = c(ξ) ξ` a.e.). -/
theorem leray_grad {f : L2V} {c : E3 → ℂ} (h : ∀ᵐ ξ, ((𝓕 f : L2V) : E3 → V) ξ = c ξ • ξc ξ) :
    leray f = 0 := by
  have : lerayF (𝓕 f) = 0 := by
    refine pmul_eq_of_ae _ _ _ ?_
    filter_upwards [h, Lp.coeFn_zero V 2 (volume : Measure E3)] with ξ hξ h0
    rw [hξ, lerSym_grad, h0]; rfl
  rw [leray, this]
  exact map_zero (Lp.fourierTransformₗᵢ E3 V).symm


/-! ## The heat semigroup `e^{τΔ}` on `L²(ℝ³; ℂ³)` (`τ = ν t`; identity for `τ ≤ 0`) -/

/-- Gaussian factor `e^{-4π² τ⁺ |ξ|²}`. -/
def gauss (τ : ℝ) (ξ : E3) : ℝ := Real.exp (-(4 * Real.pi ^ 2 * max τ 0 * ‖ξ‖ ^ 2))

lemma gauss_pos (τ : ℝ) (ξ : E3) : 0 < gauss τ ξ := Real.exp_pos _

lemma gauss_le_one (τ : ℝ) (ξ : E3) : gauss τ ξ ≤ 1 := by
  unfold gauss
  rw [Real.exp_le_one_iff, neg_nonpos]
  have := le_max_right τ 0
  positivity

lemma continuous_gauss (τ : ℝ) : Continuous (gauss τ) := by unfold gauss; fun_prop

lemma gauss_mul {σ τ : ℝ} (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (ξ : E3) :
    gauss σ ξ * gauss τ ξ = gauss (σ + τ) ξ := by
  unfold gauss
  rw [← Real.exp_add, max_eq_left hσ, max_eq_left hτ, max_eq_left (add_nonneg hσ hτ)]
  ring_nf

lemma gauss_of_nonpos {τ : ℝ} (hτ : τ ≤ 0) (ξ : E3) : gauss τ ξ = 1 := by
  unfold gauss; rw [max_eq_right hτ]; simp

/-- Heat symbol `e^{-4π²τ⁺|ξ|²} · id`. -/
def heatSym (τ : ℝ) (ξ : E3) : V →L[ℂ] V := ((gauss τ ξ : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V

lemma heatSym_apply (τ : ℝ) (ξ : E3) (v : V) : heatSym τ ξ v = ((gauss τ ξ : ℝ) : ℂ) • v := rfl

lemma heatSym_meas (τ : ℝ) (g : E3 → V) (hg : AEStronglyMeasurable g) :
    AEStronglyMeasurable (fun ξ => heatSym τ ξ (g ξ)) := by
  simp only [heatSym_apply]
  exact (Complex.continuous_ofReal.comp (continuous_gauss τ)).aestronglyMeasurable.smul hg

lemma heatSym_norm (τ : ℝ) (ξ : E3) : ‖heatSym τ ξ‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [heatSym_apply, norm_smul, Complex.norm_real, Real.norm_of_nonneg (gauss_pos τ ξ).le, one_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (gauss_le_one τ ξ)

/-- Fourier-side heat multiplier. -/
def heatF (τ : ℝ) : L2V →L[ℂ] L2V := pmul (heatSym τ) (heatSym_meas τ) (heatSym_norm τ)

/-- **Heat semigroup** `e^{τΔ} = 𝓕⁻ e^{-4π²τ|ξ|²} 𝓕`. -/
def heat (τ : ℝ) (f : L2V) : L2V := 𝓕⁻ (heatF τ (𝓕 f))

lemma fourier_heat (τ : ℝ) (f : L2V) : 𝓕 (heat τ f) = heatF τ (𝓕 f) := by
  rw [heat, fourier_fourierInv_eq]

/-- Fourier side of `e^{τΔ} f`. -/
theorem coeFn_fourier_heat (τ : ℝ) (f : L2V) :
    ((𝓕 (heat τ f) : L2V) : E3 → V) =ᵐ[volume]
      fun ξ => ((gauss τ ξ : ℝ) : ℂ) • ((𝓕 f : L2V) : E3 → V) ξ := by
  rw [fourier_heat]; exact coeFn_pmul _ _ _ _

theorem norm_heat_le (τ : ℝ) (f : L2V) : ‖heat τ f‖ ≤ ‖f‖ := by
  rw [heat, norm_fourierInv]
  exact (norm_pmul_le _ _ _ _).trans (le_of_eq (Lp.norm_fourier_eq f))

lemma heat_add_fun (τ : ℝ) (f g : L2V) : heat τ (f + g) = heat τ f + heat τ g := by
  simp only [heat, FourierAdd.fourier_add, map_add, FourierInvAdd.fourierInv_add]

lemma heat_sub (τ : ℝ) (f g : L2V) : heat τ (f - g) = heat τ f - heat τ g := by
  change (Lp.fourierTransformₗᵢ E3 V).symm (heatF τ (Lp.fourierTransformₗᵢ E3 V (f - g))) =
    (Lp.fourierTransformₗᵢ E3 V).symm (heatF τ (Lp.fourierTransformₗᵢ E3 V f)) -
    (Lp.fourierTransformₗᵢ E3 V).symm (heatF τ (Lp.fourierTransformₗᵢ E3 V g))
  simp only [map_sub]

/-- `e^{τΔ} = id` for `τ ≤ 0` (in particular `e^{0Δ} = id`). -/
theorem heat_of_nonpos {τ : ℝ} (hτ : τ ≤ 0) (f : L2V) : heat τ f = f := by
  have : heatF τ (𝓕 f) = 𝓕 f := pmul_eq_of_ae _ _ _ (Filter.Eventually.of_forall fun ξ => by
    rw [heatSym_apply, gauss_of_nonpos hτ]; simp)
  rw [heat, this, fourierInv_fourier_eq]

/-- **Semigroup law** `e^{σΔ} e^{τΔ} = e^{(σ+τ)Δ}` for `σ, τ ≥ 0`. -/
theorem heat_heat {σ τ : ℝ} (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (f : L2V) :
    heat σ (heat τ f) = heat (σ + τ) f := by
  rw [heat, fourier_heat]
  unfold heatF
  rw [pmul_pmul (heatSym σ) (heatSym τ) (heatSym (σ + τ)) (heatSym_meas σ) (heatSym_norm σ)
    (heatSym_meas τ) (heatSym_norm τ) (heatSym_meas (σ + τ)) (heatSym_norm (σ + τ))
    (fun ξ v => by rw [heatSym_apply, heatSym_apply, heatSym_apply, smul_smul, ← Complex.ofReal_mul,
      gauss_mul hσ hτ])]
  rfl

/-- `e^{τΔ}` commutes with the Leray projector. -/
theorem heat_leray (τ : ℝ) (f : L2V) : heat τ (leray f) = leray (heat τ f) := by
  rw [heat, leray, fourier_fourierInv_eq, leray, fourier_heat]
  unfold heatF lerayF
  rw [pmul_pmul (heatSym τ) lerSym (fun ξ => (heatSym τ ξ).comp (lerSym ξ)) (heatSym_meas τ)
    (heatSym_norm τ) lerSym_meas lerSym_norm
    (fun g hg => by simpa using heatSym_meas τ _ (lerSym_meas g hg))
    (fun ξ => (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by nlinarith [heatSym_norm τ ξ, lerSym_norm ξ, norm_nonneg (heatSym τ ξ),
        norm_nonneg (lerSym ξ)]))
    (fun ξ v => rfl),
    pmul_pmul lerSym (heatSym τ) (fun ξ => (heatSym τ ξ).comp (lerSym ξ)) lerSym_meas lerSym_norm
    (heatSym_meas τ) (heatSym_norm τ)
    (fun g hg => by simpa using heatSym_meas τ _ (lerSym_meas g hg))
    (fun ξ => (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by nlinarith [heatSym_norm τ ξ, lerSym_norm ξ, norm_nonneg (heatSym τ ξ),
        norm_nonneg (lerSym ξ)]))
    (fun ξ v => by rw [ContinuousLinearMap.comp_apply, heatSym_apply, heatSym_apply, map_smul])]

lemma heat_max (τ : ℝ) (f : L2V) : heat τ f = heat (max τ 0) f := by
  have : heatSym τ = heatSym (max τ 0) := by
    funext ξ; simp only [heatSym, gauss, max_eq_left (le_max_right τ 0)]
  simp only [heat, heatF, this]

/-- Fourier-side strong continuity at `τ = 0`. -/
theorem tendsto_heatF_zero (g : L2V) :
    Filter.Tendsto (fun τ => heatF τ g) (nhds 0) (nhds g) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have key : ∀ τ, (⇑(heatF τ g) - ⇑g) =ᵐ[volume]
      fun ξ => (((gauss τ ξ - 1 : ℝ)) : ℂ) • (g : E3 → V) ξ := by
    intro τ
    filter_upwards [coeFn_pmul (heatSym τ) (heatSym_meas τ) (heatSym_norm τ) g] with ξ h
    rw [Pi.sub_apply, show (heatF τ g : E3 → V) ξ = _ from h, heatSym_apply, Complex.ofReal_sub,
      sub_smul, Complex.ofReal_one, one_smul]
  have hg : Measurable (g : E3 → V) := (Lp.stronglyMeasurable g).measurable
  have hlim : Filter.Tendsto (fun τ => ∫⁻ ξ, ‖(((gauss τ ξ - 1 : ℝ)) : ℂ) • (g : E3 → V) ξ‖ₑ ^
      ((2 : ENNReal).toReal)) (nhds 0) (nhds 0) := by
    have := MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence (μ := volume)
      (l := nhds (0 : ℝ)) (f := fun _ => 0)
      (F := fun τ ξ => ‖(((gauss τ ξ - 1 : ℝ)) : ℂ) • (g : E3 → V) ξ‖ₑ ^ ((2 : ENNReal).toReal))
      (fun ξ => ‖(g : E3 → V) ξ‖ₑ ^ ((2 : ENNReal).toReal))
      (Filter.Eventually.of_forall fun τ => by
        have hc : Continuous fun ξ => (((gauss τ ξ - 1 : ℝ)) : ℂ) :=
          Complex.continuous_ofReal.comp ((continuous_gauss τ).sub continuous_const)
        exact ((hc.measurable.smul hg).enorm).pow_const _)
      (Filter.Eventually.of_forall fun τ => Filter.Eventually.of_forall fun ξ => by
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        rw [enorm_smul]
        refine mul_le_of_le_one_left' ?_
        rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_le_one, Complex.norm_real, Real.norm_eq_abs,
          abs_le]
        constructor <;> linarith [gauss_pos τ ξ, gauss_le_one τ ξ])
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
        (Lp.eLpNorm_lt_top g)).ne
      (Filter.Eventually.of_forall fun ξ => by
        have hc : Continuous fun τ => ‖(((gauss τ ξ - 1 : ℝ)) : ℂ) • (g : E3 → V) ξ‖ₑ ^
            ((2 : ENNReal).toReal) := by
          refine ENNReal.continuous_rpow_const.comp (continuous_enorm.comp ?_)
          refine Continuous.smul (Complex.continuous_ofReal.comp ?_) continuous_const
          unfold gauss; fun_prop
        have h0 := hc.tendsto 0
        simpa [gauss_of_nonpos le_rfl] using h0)
    simpa using this
  have h2 := (ENNReal.continuous_rpow_const (y := 1 / (2 : ENNReal).toReal)).tendsto 0 |>.comp hlim
  have h3 : (0 : ENNReal) ^ (1 / (2 : ENNReal).toReal) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
  rw [h3] at h2
  refine h2.congr fun τ => ?_
  simp only [Function.comp_apply]
  rw [eLpNorm_congr_ae (key τ),
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]

/-- Strong continuity of `e^{τΔ}` at `τ = 0`. -/
theorem tendsto_heat_zero (f : L2V) : Filter.Tendsto (fun τ => heat τ f) (nhds 0) (nhds f) := by
  have hc : Continuous (fun g : L2V => 𝓕⁻ g) := (Lp.fourierTransformₗᵢ E3 V).symm.continuous
  have := (hc.tendsto _).comp (tendsto_heatF_zero (𝓕 f))
  rw [fourierInv_fourier_eq] at this
  exact this

lemma norm_heat_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (f : L2V) :
    ‖heat a f - heat b f‖ ≤ ‖heat |a - b| f - f‖ := by
  rcases le_total b a with h | h
  · have e : heat a f = heat b (heat (a - b) f) := by
      rw [heat_heat hb (sub_nonneg.2 h)]; congr 1; ring
    rw [e, ← heat_sub, abs_of_nonneg (sub_nonneg.2 h)]
    exact norm_heat_le _ _
  · have e : heat b f = heat a (heat (b - a) f) := by
      rw [heat_heat ha (sub_nonneg.2 h)]; congr 1; ring
    rw [e, norm_sub_rev, ← heat_sub, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)]
    exact norm_heat_le _ _

/-- **Strong continuity** of the heat semigroup: `τ ↦ e^{τΔ} f` is continuous `ℝ → L²`. -/
theorem continuous_heat (f : L2V) : Continuous (fun τ => heat τ f) := by
  rw [continuous_iff_continuousAt]
  intro t
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hh : Filter.Tendsto (fun s => |max s 0 - max t 0|) (nhds t) (nhds 0) := by
    have : Continuous fun s : ℝ => |max s 0 - max t 0| := by fun_prop
    simpa using this.tendsto t
  have hT := (tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_heat_zero f)).comp hh
  refine squeeze_zero (fun _ => norm_nonneg _) (fun s => ?_) hT
  rw [heat_max s, heat_max t]
  exact norm_heat_sub_le (le_max_right _ _) (le_max_right _ _) f

end LerayHeat

#print axioms LerayHeat.norm_leray_le
#print axioms LerayHeat.leray_leray
#print axioms LerayHeat.inner_leray
#print axioms LerayHeat.leray_divFree
#print axioms LerayHeat.leray_eq_self
#print axioms LerayHeat.leray_grad
#print axioms LerayHeat.coeFn_fourier_heat
#print axioms LerayHeat.norm_heat_le
#print axioms LerayHeat.heat_of_nonpos
#print axioms LerayHeat.heat_heat
#print axioms LerayHeat.heat_leray
#print axioms LerayHeat.tendsto_heat_zero
#print axioms LerayHeat.continuous_heat
