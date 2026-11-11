import Scratch.FourierCutoff

/-! # Frequency-truncated BKM log bound: Fourier-multiplier blocks

Block operator `mult P h x = ∫ 𝐞⟪ξ,x⟫ P(ξ) 𝓕h(ξ) dξ`. For integrable `P` it is convolution with
`𝓕⁻P`, so `|mult P h x| ≤ ‖𝓕⁻P‖₁ · sup|h|`, and dilating `P` does not change `‖𝓕⁻P‖₁`. -/

open MeasureTheory SchwartzMap FourierTransform Real
open scoped ENNReal ContDiff InnerProductSpace

noncomputable section
namespace LogBound

open FourierEmb

/-- Fourier multiplier applied at a point. -/
def mult (P : E3 → ℂ) (h : E3 → ℂ) (x : E3) : ℂ := ∫ ξ, 𝐞 (⟪ξ, x⟫_ℝ) • (P ξ * 𝓕 h ξ)

lemma mult_eq_conv {P : E3 → ℂ} (hP : Integrable P) (h : 𝓢(E3, ℂ)) (x : E3) :
    mult P h x = ∫ y, 𝓕⁻ P (x - y) * h y := by
  have hf : Integrable (fun ξ : E3 => 𝐞 (⟪ξ, x⟫_ℝ) • P ξ) := by
    refine (hP.norm.mono' ?_ (Filter.Eventually.of_forall fun ξ => ?_))
    · exact (Continuous.aestronglyMeasurable (by fun_prop)).smul hP.aestronglyMeasurable
    · rw [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul]
  have key := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := 𝐞) (μ := volume)
    (ν := volume) (L := innerₗ E3) Real.continuous_fourierChar
    (by simp only [innerₗ_apply_apply]; exact continuous_inner) hf h.integrable
  have h1 : ∀ y, VectorFourier.fourierIntegral 𝐞 volume (innerₗ E3)
      (fun ξ : E3 => 𝐞 (⟪ξ, x⟫_ℝ) • P ξ) y = 𝓕⁻ P (x - y) := by
    intro y
    rw [Real.fourierInv_eq, VectorFourier.fourierIntegral]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [innerₗ_apply_apply, smul_smul]
    rw [← AddChar.map_add_eq_mul, inner_sub_right]
    congr 2; ring
  have h2 : ∀ ξ, VectorFourier.fourierIntegral 𝐞 volume (innerₗ E3).flip (⇑h) ξ = 𝓕 h ξ := by
    intro ξ
    rw [SchwartzMap.fourier_coe, Real.fourier_eq, VectorFourier.fourierIntegral]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp [real_inner_comm]
  simp only [h1, h2] at key
  unfold mult
  rw [show (∫ y, 𝓕⁻ P (x - y) * h y) = ∫ y, 𝓕⁻ P (x - y) • h y from rfl, key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [SchwartzMap.fourier_coe, smul_mul_assoc, smul_eq_mul]


/-- `|mult P h x| ≤ ‖𝓕⁻P‖₁ · sup|h|`. -/
lemma norm_mult_le {P : E3 → ℂ} (hP : Integrable P) (hk : Integrable (𝓕⁻ P)) (h : 𝓢(E3, ℂ))
    {B : ℝ} (hB : ∀ y, ‖h y‖ ≤ B) (x : E3) :
    ‖mult P h x‖ ≤ (∫ z, ‖𝓕⁻ P z‖) * B := by
  rw [mult_eq_conv hP h x]
  have hg : Integrable (fun y => ‖𝓕⁻ P (x - y)‖ * B) :=
    ((hk.comp_sub_left x).norm.mul_const B)
  refine (norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall fun y => ?_)).trans ?_
  · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hB y) (norm_nonneg _)
  · rw [integral_mul_const, integral_sub_left_eq_self (fun z => ‖𝓕⁻ P z‖) volume x]

lemma finrank_E3 : Module.finrank ℝ E3 = 3 := finrank_euclideanSpace_fin

set_option backward.isDefEq.respectTransparency false in
/-- Dilation: `𝓕⁻(Q(c⁻¹·))(z) = c³ 𝓕⁻Q(c z)`. -/
lemma fourierInv_dilate (Q : E3 → ℂ) {c : ℝ} (hc : 0 < c) (z : E3) :
    𝓕⁻ (fun ξ => Q (c⁻¹ • ξ)) z = (c ^ 3 : ℝ) • 𝓕⁻ Q (c • z) := by
  rw [Real.fourierInv_eq, Real.fourierInv_eq]
  have := Measure.integral_comp_smul (μ := volume) (fun ξ : E3 => 𝐞 (⟪ξ, z⟫_ℝ) • Q (c⁻¹ • ξ)) c
  rw [finrank_E3] at this
  have hc3 : (0:ℝ) < c ^ 3 := by positivity
  rw [abs_of_pos (inv_pos.mpr hc3)] at this
  have e1 : (∫ ξ : E3, 𝐞 (⟪ξ, z⟫_ℝ) • Q (c⁻¹ • ξ)) = (c ^ 3 : ℝ) •
      ∫ η : E3, 𝐞 (⟪c • η, z⟫_ℝ) • Q (c⁻¹ • c • η) := by
    rw [this, smul_inv_smul₀ hc3.ne']
  rw [e1]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  simp only [smul_smul, inv_mul_cancel₀ hc.ne', one_smul, real_inner_smul_left,
    real_inner_smul_right]

set_option backward.isDefEq.respectTransparency false in
lemma integrable_fourierInv_dilate {Q : E3 → ℂ} (hk : Integrable (𝓕⁻ Q)) {c : ℝ} (hc : 0 < c) :
    Integrable (𝓕⁻ (fun ξ => Q (c⁻¹ • ξ))) := by
  have : 𝓕⁻ (fun ξ => Q (c⁻¹ • ξ)) = fun z => (c ^ 3 : ℝ) • 𝓕⁻ Q (c • z) :=
    funext (fourierInv_dilate Q hc)
  rw [this]
  exact (hk.comp_smul hc.ne').smul (c ^ 3 : ℝ)

set_option backward.isDefEq.respectTransparency false in
/-- Dilation leaves the kernel's `L¹` norm unchanged. -/
lemma integral_norm_fourierInv_dilate (Q : E3 → ℂ) {c : ℝ} (hc : 0 < c) :
    (∫ z, ‖𝓕⁻ (fun ξ => Q (c⁻¹ • ξ)) z‖) = ∫ z, ‖𝓕⁻ Q z‖ := by
  have hc3' : (0:ℝ) < c ^ 3 := by positivity
  have hp : ∀ z, ‖𝓕⁻ (fun ξ => Q (c⁻¹ • ξ)) z‖ = c ^ 3 * ‖𝓕⁻ Q (c • z)‖ := fun z => by
    rw [fourierInv_dilate Q hc, Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hc3']
  simp_rw [hp]
  rw [integral_const_mul, Measure.integral_comp_smul (μ := volume) (fun z => ‖𝓕⁻ Q z‖) c, finrank_E3]
  have hc3 : (0:ℝ) < c ^ 3 := by positivity
  rw [abs_of_pos (inv_pos.mpr hc3), smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hc3.ne', one_mul]


/-! ## Littlewood–Paley cutoffs and Riesz-type symbols -/

/-- Smooth cutoff: `= 1` on `‖ξ‖ ≤ 1`, supported in `‖ξ‖ < 2`, values in `[0,1]`. -/
def ρ : ContDiffBump (0 : E3) := ⟨1, 2, one_pos, one_lt_two⟩

/-- Dyadic annulus function `ψ ξ = ρ(ξ/2) - ρ(ξ)`. -/
def ψ (ξ : E3) : ℝ := ρ ((2 : ℝ)⁻¹ • ξ) - ρ ξ

lemma ρ_eq_one {ξ : E3} (h : ‖ξ‖ ≤ 1) : ρ ξ = 1 :=
  ρ.one_of_mem_closedBall (by simpa [ρ] using h)

lemma ρ_eq_zero {ξ : E3} (h : 2 ≤ ‖ξ‖) : ρ ξ = 0 := by
  refine ρ.zero_of_le_dist ?_
  simpa [ρ] using h

lemma ψ_eq_zero_of_le {ξ : E3} (h : ‖ξ‖ < 1) : ψ ξ = 0 := by
  unfold ψ
  rw [ρ_eq_one h.le, ρ_eq_one]; · ring
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]; linarith [norm_nonneg ξ]

lemma ψ_eq_zero_of_ge {ξ : E3} (h : 4 ≤ ‖ξ‖) : ψ ξ = 0 := by
  have h1 : 2 ≤ ‖(2 : ℝ)⁻¹ • ξ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]; linarith
  unfold ψ
  rw [ρ_eq_zero h1, ρ_eq_zero (by linarith)]; ring

lemma contDiff_ρ : ContDiff ℝ ∞ (fun ξ : E3 => ρ ξ) := ρ.contDiff

lemma contDiff_ψ : ContDiff ℝ ∞ ψ := by
  unfold ψ
  exact (contDiff_ρ.comp (contDiff_const_smul _)).sub contDiff_ρ

/-- Riesz-type symbol `ξ_k ξ_l / ‖ξ‖²` (homogeneous of degree 0). -/
def msym (k l : Fin 3) (ξ : E3) : ℝ := ξ k * ξ l / ‖ξ‖ ^ 2

lemma msym_smul (k l : Fin 3) {c : ℝ} (hc : c ≠ 0) (ξ : E3) : msym k l (c • ξ) = msym k l ξ := by
  unfold msym
  simp only [PiLp.smul_apply, smul_eq_mul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  by_cases hξ : ‖ξ‖ = 0
  · simp [hξ]
  · field_simp

/-- Annulus block symbol `Q_{kl} = ψ · msym k l`, as a complex function. -/
def Q (k l : Fin 3) (ξ : E3) : ℂ := ((ψ ξ * msym k l ξ : ℝ) : ℂ)

lemma contDiff_Q (k l : Fin 3) : ContDiff ℝ ∞ (Q k l) := by
  have hr : ContDiff ℝ ∞ (fun ξ => ψ ξ * msym k l ξ) := by
    rw [contDiff_iff_contDiffAt]
    intro ξ
    by_cases hξ : ‖ξ‖ < 1
    · have : (fun ξ => ψ ξ * msym k l ξ) =ᶠ[nhds ξ] fun _ => 0 := by
        have ho : IsOpen {η : E3 | ‖η‖ < 1} := isOpen_lt continuous_norm continuous_const
        filter_upwards [ho.mem_nhds hξ] with η hη
        rw [ψ_eq_zero_of_le hη, zero_mul]
      exact (contDiffAt_const).congr_of_eventuallyEq this
    · have hne : ‖ξ‖ ^ 2 ≠ 0 := by push Not at hξ; positivity
      refine contDiff_ψ.contDiffAt.mul ?_
      unfold msym
      refine ContDiffAt.div ?_ (contDiff_norm_sq ℝ).contDiffAt hne
      exact ((EuclideanSpace.proj k : E3 →L[ℝ] ℝ).contDiff.mul
        (EuclideanSpace.proj l : E3 →L[ℝ] ℝ).contDiff).contDiffAt
  exact Complex.ofRealCLM.contDiff.comp hr

lemma hasCompactSupport_Q (k l : Fin 3) : HasCompactSupport (Q k l) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : E3) 4) fun ξ hξ => ?_
  have : 4 ≤ ‖ξ‖ := by simp at hξ; linarith
  simp [Q, ψ_eq_zero_of_ge this]

/-- `Q_{kl}` as a Schwartz function. -/
def QS (k l : Fin 3) : 𝓢(E3, ℂ) := (hasCompactSupport_Q k l).toSchwartzMap (contDiff_Q k l)

lemma QS_apply (k l : Fin 3) (ξ : E3) : QS k l ξ = Q k l ξ := rfl

lemma integrable_Q (k l : Fin 3) : Integrable (Q k l) := (QS k l).integrable

lemma integrable_fourierInv_Q (k l : Fin 3) : Integrable (𝓕⁻ (Q k l)) := by
  have : 𝓕⁻ (Q k l) = ⇑(𝓕⁻ (QS k l) : 𝓢(E3, ℂ)) := by
    rw [fourierInv_coe]; rfl
  rw [this]; exact (𝓕⁻ (QS k l) : 𝓢(E3, ℂ)).integrable

/-- Uniform kernel constant `A = max_{k,l} ‖𝓕⁻ Q_{kl}‖₁`. -/
def Akern : ℝ := ∑ k : Fin 3, ∑ l : Fin 3, ∫ z, ‖𝓕⁻ (Q k l) z‖

lemma kern_le_Akern (k l : Fin 3) : (∫ z, ‖𝓕⁻ (Q k l) z‖) ≤ Akern := by
  have h0 : ∀ k l, 0 ≤ ∫ z, ‖𝓕⁻ (Q k l) z‖ := fun k l => integral_nonneg fun _ => norm_nonneg _
  unfold Akern
  calc (∫ z, ‖𝓕⁻ (Q k l) z‖) ≤ ∑ l' : Fin 3, ∫ z, ‖𝓕⁻ (Q k l') z‖ :=
        Finset.single_le_sum (f := fun l' => ∫ z, ‖𝓕⁻ (Q k l') z‖) (fun l' _ => h0 k l')
          (Finset.mem_univ l)
    _ ≤ _ := Finset.single_le_sum (f := fun k' => ∑ l' : Fin 3, ∫ z, ‖𝓕⁻ (Q k' l') z‖)
          (fun k' _ => Finset.sum_nonneg fun l' _ => h0 k' l') (Finset.mem_univ k)

/-- **Dyadic block bound, uniform in the scale.** -/
lemma norm_mult_Q_dilate_le (k l : Fin 3) {c : ℝ} (hc : 0 < c) (h : 𝓢(E3, ℂ)) {B : ℝ}
    (hB : ∀ y, ‖h y‖ ≤ B) (x : E3) :
    ‖mult (fun ξ => Q k l (c⁻¹ • ξ)) h x‖ ≤ Akern * B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hP : Integrable (fun ξ => Q k l (c⁻¹ • ξ)) :=
    (integrable_Q k l).comp_smul (inv_ne_zero hc.ne')
  refine (norm_mult_le hP (integrable_fourierInv_dilate (integrable_fourierInv_Q k l) hc) h hB x).trans ?_
  rw [integral_norm_fourierInv_dilate _ hc]
  exact mul_le_mul_of_nonneg_right (kern_le_Akern k l) hB0

end LogBound
