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


/-! ## Fourier side of coordinate derivatives and the Helmholtz identity -/

open LineDeriv

/-- Coordinate unit vector. -/
abbrev eb (m : Fin 3) : E3 := EuclideanSpace.single m (1 : ℝ)

set_option backward.isDefEq.respectTransparency false in
lemma fourier_D (f : 𝓢(E3, ℂ)) (m : Fin 3) (ξ : E3) :
    𝓕 (∂_{eb m} f) ξ = (2 * π * Complex.I) * ((ξ m : ℝ) : ℂ) * 𝓕 f ξ := by
  have hT : (fun y : E3 => ⟪y, eb m⟫_ℝ).HasTemperateGrowth :=
    ((innerSL ℝ).flip (eb m)).hasTemperateGrowth
  rw [fourier_lineDerivOp_eq, SchwartzMap.smul_apply, smulLeftCLM_apply_apply hT]
  simp [EuclideanSpace.inner_single_right, Complex.real_smul, mul_assoc]

lemma norm_sq_E3 (ξ : E3) : ‖ξ‖ ^ 2 = ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

/-- Pointwise Helmholtz identity on an annulus block (`ξ ≠ 0` or `ψ = 0`). -/
lemma block_identity (g : Fin 3 → 𝓢(E3, ℂ)) (k l : Fin 3) {c : ℝ} (hc : 0 < c) (ξ : E3) :
    ((ψ (c⁻¹ • ξ) : ℝ) : ℂ) * 𝓕 (∂_{eb k} (g l)) ξ =
      (∑ m : Fin 3, Q k m (c⁻¹ • ξ) * 𝓕 (∂_{eb m} (g l) - ∂_{eb l} (g m)) ξ) +
        Q k l (c⁻¹ • ξ) * 𝓕 (∑ m : Fin 3, ∂_{eb m} (g m)) ξ := by
  by_cases hψ : ψ (c⁻¹ • ξ) = 0
  · simp [Q, hψ]
  have hξ : ‖ξ‖ ^ 2 ≠ 0 := by
    have : ξ ≠ 0 := by rintro rfl; exact hψ (by simp [ψ_eq_zero_of_le])
    positivity
  simp only [Q, msym_smul _ _ (inv_ne_zero hc.ne'), sub_eq_add_neg,
    FourierAdd.fourier_add, FourierTransform.fourier_neg, SchwartzMap.add_apply,
    SchwartzMap.neg_apply, fourier_D, Fin.sum_univ_three]
  unfold msym
  rw [norm_sq_E3] at hξ ⊢
  push_cast
  have hξc : ((ξ 0 : ℂ) ^ 2 + (ξ 1 : ℂ) ^ 2 + (ξ 2 : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hξ
  field_simp
  fin_cases k <;> fin_cases l <;> simp <;> ring


/-! ## Littlewood–Paley splitting of Fourier inversion -/

lemma inversion (h : 𝓢(E3, ℂ)) (x : E3) : h x = ∫ ξ, 𝐞 (⟪ξ, x⟫_ℝ) • 𝓕 h ξ := by
  have h1 : h x = 𝓕⁻ (𝓕 h) x := by rw [fourierInv_fourier_eq]
  rw [h1, fourierInv_coe, Real.fourierInv_eq]

lemma integrable_coef (h : 𝓢(E3, ℂ)) {a : E3 → ℂ} (ha : Continuous a) {C : ℝ}
    (hC : ∀ ξ, ‖a ξ‖ ≤ C) (x : E3) :
    Integrable (fun ξ => 𝐞 (⟪ξ, x⟫_ℝ) • (a ξ * 𝓕 h ξ)) := by
  refine Integrable.mono' ((𝓕 h).integrable.norm.const_mul C) ?_
    (Filter.Eventually.of_forall fun ξ => ?_)
  · exact (Continuous.aestronglyMeasurable (by
      have := (𝓕 h).continuous
      fun_prop))
  · rw [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right (hC ξ) (norm_nonneg _)

/-- Low, dyadic and high coefficient functions. -/
def lowP (ξ : E3) : ℂ := ((ρ ξ : ℝ) : ℂ)
def midP (j : ℕ) (ξ : E3) : ℂ := ((ψ (((2 : ℝ) ^ j)⁻¹ • ξ) : ℝ) : ℂ)
def highP (N : ℕ) (ξ : E3) : ℂ := ((1 - ρ (((2 : ℝ) ^ N)⁻¹ • ξ) : ℝ) : ℂ)

lemma telescope (N : ℕ) (ξ : E3) :
    lowP ξ + ∑ j ∈ Finset.range N, midP j ξ + highP N ξ = 1 := by
  have hψ : ∀ j : ℕ, ψ (((2 : ℝ) ^ j)⁻¹ • ξ) =
      ρ (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) - ρ (((2 : ℝ) ^ j)⁻¹ • ξ) := fun j => by
    unfold ψ; rw [smul_smul, pow_succ, mul_inv, mul_comm]
  have hs := Finset.sum_range_sub (fun j => ρ (((2 : ℝ) ^ j)⁻¹ • ξ)) N
  simp only [lowP, midP, highP]
  rw [← Complex.ofReal_sum]
  simp only [hψ, hs, pow_zero, inv_one, one_smul]
  push_cast; ring

lemma continuous_lowP : Continuous lowP := by
  unfold lowP; exact Complex.continuous_ofReal.comp ρ.continuous
lemma continuous_midP (j : ℕ) : Continuous (midP j) := by
  unfold midP; exact Complex.continuous_ofReal.comp
    (contDiff_ψ.continuous.comp (continuous_const_smul _))
lemma continuous_highP (N : ℕ) : Continuous (highP N) := by
  unfold highP; exact Complex.continuous_ofReal.comp
    (continuous_const.sub (ρ.continuous.comp (continuous_const_smul _)))

lemma norm_lowP_le (ξ : E3) : ‖lowP ξ‖ ≤ 1 := by
  rw [lowP, Complex.norm_real, Real.norm_of_nonneg ρ.nonneg]; exact ρ.le_one
lemma norm_midP_le (j : ℕ) (ξ : E3) : ‖midP j ξ‖ ≤ 1 := by
  rw [midP, Complex.norm_real, Real.norm_eq_abs, abs_le]; unfold ψ
  constructor <;> linarith [ρ.nonneg (x := ((2:ℝ)⁻¹ • ((2 : ℝ) ^ j)⁻¹ • ξ)),
    ρ.le_one (x := ((2:ℝ)⁻¹ • ((2 : ℝ) ^ j)⁻¹ • ξ)), ρ.nonneg (x := ((2 : ℝ) ^ j)⁻¹ • ξ),
    ρ.le_one (x := ((2 : ℝ) ^ j)⁻¹ • ξ)]
lemma norm_highP_le (N : ℕ) (ξ : E3) : ‖highP N ξ‖ ≤ 1 := by
  rw [highP, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [ρ.nonneg (x := ((2 : ℝ) ^ N)⁻¹ • ξ),
    ρ.le_one (x := ((2 : ℝ) ^ N)⁻¹ • ξ)]

/-- `h x = low + ∑_{j<N} block_j + high`. -/
lemma lp_split (h : 𝓢(E3, ℂ)) (N : ℕ) (x : E3) :
    h x = (∫ ξ, 𝐞 (⟪ξ, x⟫_ℝ) • (lowP ξ * 𝓕 h ξ)) +
      ∑ j ∈ Finset.range N, (∫ ξ, 𝐞 (⟪ξ, x⟫_ℝ) • (midP j ξ * 𝓕 h ξ)) +
      ∫ ξ, 𝐞 (⟪ξ, x⟫_ℝ) • (highP N ξ * 𝓕 h ξ) := by
  have hL := integrable_coef h continuous_lowP norm_lowP_le x
  have hM := fun j => integrable_coef h (continuous_midP j) (norm_midP_le j) x
  have hH := integrable_coef h (continuous_highP N) (norm_highP_le N) x
  have hS : Integrable (fun ξ => ∑ j ∈ Finset.range N, 𝐞 (⟪ξ, x⟫_ℝ) • (midP j ξ * 𝓕 h ξ)) :=
    integrable_finset_sum _ fun j _ => hM j
  calc h x = ∫ ξ, ((𝐞 (⟪ξ, x⟫_ℝ) • (lowP ξ * 𝓕 h ξ) +
        ∑ j ∈ Finset.range N, 𝐞 (⟪ξ, x⟫_ℝ) • (midP j ξ * 𝓕 h ξ)) +
        𝐞 (⟪ξ, x⟫_ℝ) • (highP N ξ * 𝓕 h ξ)) := by
        rw [inversion h x]
        refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
        simp only
        rw [← Finset.smul_sum, ← smul_add, ← smul_add, ← Finset.sum_mul, ← add_mul, ← add_mul,
          telescope, one_mul]
    _ = _ := by
        have hLS : Integrable (fun ξ => 𝐞 (⟪ξ, x⟫_ℝ) • (lowP ξ * 𝓕 h ξ) +
            ∑ j ∈ Finset.range N, 𝐞 (⟪ξ, x⟫_ℝ) • (midP j ξ * 𝓕 h ξ)) := hL.add hS
        rw [integral_add hLS hH, integral_add hL hS, integral_finset_sum _ fun j _ => hM j]


/-! ## Dyadic blocks of `∂_k g_l` are controlled by curl and divergence -/

lemma integrable_mult_Q (k l : Fin 3) {c : ℝ} (h : 𝓢(E3, ℂ)) (x : E3) :
    Integrable (fun ξ => 𝐞 (⟪ξ, x⟫_ℝ) • (Q k l (c⁻¹ • ξ) * 𝓕 h ξ)) :=
  integrable_coef h ((contDiff_Q k l).continuous.comp (continuous_const_smul _))
    (fun ξ => (QS k l).norm_le_seminorm ℝ (c⁻¹ • ξ)) x

lemma mid_eq (g : Fin 3 → 𝓢(E3, ℂ)) (k l : Fin 3) (j : ℕ) (x : E3) :
    (∫ ξ, 𝐞 (⟪ξ, x⟫_ℝ) • (midP j ξ * 𝓕 (∂_{eb k} (g l)) ξ)) =
      (∑ m : Fin 3, mult (fun ξ => Q k m (((2 : ℝ) ^ j)⁻¹ • ξ))
          ⇑(∂_{eb m} (g l) - ∂_{eb l} (g m)) x) +
        mult (fun ξ => Q k l (((2 : ℝ) ^ j)⁻¹ • ξ)) ⇑(∑ m : Fin 3, ∂_{eb m} (g m) : 𝓢(E3, ℂ)) x := by
  have hc : (0 : ℝ) < 2 ^ j := by positivity
  unfold mult
  have hI := fun m => integrable_mult_Q k m (c := (2 : ℝ) ^ j)
    (∂_{eb m} (g l) - ∂_{eb l} (g m)) x
  have hS : Integrable (fun ξ => ∑ m : Fin 3, 𝐞 (⟪ξ, x⟫_ℝ) •
      (Q k m (((2 : ℝ) ^ j)⁻¹ • ξ) * 𝓕 (∂_{eb m} (g l) - ∂_{eb l} (g m)) ξ)) :=
    integrable_finset_sum _ fun m _ => hI m
  calc _ = ∫ ξ, ((∑ m : Fin 3, 𝐞 (⟪ξ, x⟫_ℝ) •
        (Q k m (((2 : ℝ) ^ j)⁻¹ • ξ) * 𝓕 (∂_{eb m} (g l) - ∂_{eb l} (g m)) ξ)) +
        𝐞 (⟪ξ, x⟫_ℝ) • (Q k l (((2 : ℝ) ^ j)⁻¹ • ξ) *
          𝓕 (∑ m : Fin 3, ∂_{eb m} (g m) : 𝓢(E3, ℂ)) ξ)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
        simp only [midP]
        rw [← Finset.smul_sum, ← smul_add]
        exact congrArg _ (block_identity g k l hc ξ)
    _ = _ := by
        rw [integral_add hS (integrable_mult_Q k l _ x), integral_finset_sum _ fun m _ => hI m]
        rfl

lemma norm_mid_le (g : Fin 3 → 𝓢(E3, ℂ)) (k l : Fin 3) (j : ℕ) {Bω Bd : ℝ}
    (hω : ∀ m y, ‖(∂_{eb m} (g l) - ∂_{eb l} (g m)) y‖ ≤ Bω)
    (hd : ∀ y, ‖(∑ m : Fin 3, ∂_{eb m} (g m)) y‖ ≤ Bd) (x : E3) :
    ‖∫ ξ, 𝐞 (⟪ξ, x⟫_ℝ) • (midP j ξ * 𝓕 (∂_{eb k} (g l)) ξ)‖ ≤ Akern * (3 * Bω + Bd) := by
  have hc : (0 : ℝ) < 2 ^ j := by positivity
  rw [mid_eq]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖∑ m : Fin 3, mult (fun ξ => Q k m (((2 : ℝ) ^ j)⁻¹ • ξ))
      ⇑(∂_{eb m} (g l) - ∂_{eb l} (g m)) x‖ ≤ 3 * (Akern * Bω) := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _m : Fin 3, Akern * Bω :=
          Finset.sum_le_sum fun m _ => norm_mult_Q_dilate_le k m hc _ (hω m) x
      _ = _ := by simp
  have h2 := norm_mult_Q_dilate_le k l hc _ hd x
  nlinarith


/-! ## Low-frequency piece: controlled by `‖f‖₂` -/

/-- `C_low = (∫ (4π ρ)²)^{1/2}`. -/
def Clow : ℝ≥0∞ := (∫⁻ ξ : E3, ENNReal.ofReal (4 * π * ρ ξ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

lemma Clow_ne_top : Clow ≠ ⊤ := by
  refine ENNReal.rpow_ne_top_of_nonneg (by norm_num) ?_
  have hc : Continuous (fun ξ : E3 => (4 * π * ρ ξ) ^ 2) := by
    have := ρ.continuous; fun_prop
  have hs : HasCompactSupport (fun ξ : E3 => (4 * π * ρ ξ) ^ 2) := by
    have h1 : HasCompactSupport (fun ξ : E3 => ρ ξ) := ρ.hasCompactSupport
    exact (h1.mul_left (f := fun _ => 4 * π)).comp_left (g := fun r : ℝ => r ^ 2) (by simp)
  have hi := hc.integrable_of_hasCompactSupport (μ := volume) hs
  refine ne_of_lt (lt_of_le_of_lt (le_of_eq (lintegral_congr fun ξ => ?_)) hi.lintegral_lt_top)
  rw [ENNReal.ofReal_rpow_of_nonneg (by have := ρ.nonneg (x := ξ); positivity) (by norm_num)]
  norm_cast

lemma low_pt (f : 𝓢(E3, ℂ)) (k : Fin 3) (ξ : E3) :
    ‖lowP ξ * 𝓕 (∂_{eb k} f) ξ‖ₑ ≤ ENNReal.ofReal (4 * π * ρ ξ) * ‖𝓕 f ξ‖ₑ := by
  have hρ := ρ.nonneg (x := ξ)
  have key : ‖lowP ξ * 𝓕 (∂_{eb k} f) ξ‖ ≤ 4 * π * ρ ξ * ‖𝓕 f ξ‖ := by
    rw [fourier_D, lowP, norm_mul, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hρ, Complex.norm_real]
    have h2 : ‖(2 * π * Complex.I : ℂ)‖ = 2 * π := by
      rw [norm_mul, Complex.norm_I, mul_one, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg pi_pos.le]; norm_num
    rw [h2]
    have hk : ρ ξ * ‖ξ k‖ ≤ ρ ξ * 2 := by
      by_cases hξ : 2 ≤ ‖ξ‖
      · rw [ρ_eq_zero hξ]; simp
      · push Not at hξ
        exact mul_le_mul_of_nonneg_left ((PiLp.norm_apply_le ξ k).trans hξ.le) hρ
    have hF := norm_nonneg (𝓕 f ξ)
    nlinarith [pi_pos, mul_le_mul_of_nonneg_right hk (mul_nonneg (by positivity : (0:ℝ) ≤ 2 * π) hF)]
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal key

lemma enorm_integral_char_le (F : E3 → ℂ) (x : E3) :
    ‖∫ ξ, 𝐞 (⟪ξ, x⟫_ℝ) • F ξ‖ₑ ≤ ∫⁻ ξ, ‖F ξ‖ₑ := by
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun ξ => ?_))
  rw [Circle.smul_def, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, norm_smul,
    Circle.norm_coe, one_mul]

/-- **Low-frequency bound**: `|low| ≤ C_low ‖f‖₂`. -/
lemma low_le (f : 𝓢(E3, ℂ)) (k : Fin 3) (x : E3) :
    ‖∫ ξ, 𝐞 (⟪ξ, x⟫_ℝ) • (lowP ξ * 𝓕 (∂_{eb k} f) ξ)‖ₑ ≤
      Clow * (∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  have hm1 : AEMeasurable (fun ξ : E3 => ENNReal.ofReal (4 * π * ρ ξ)) :=
    (ENNReal.measurable_ofReal.comp (by
      have := ρ.continuous
      exact (continuous_const.mul this).measurable)).aemeasurable
  have hm2 : AEMeasurable (fun ξ => ‖𝓕 f ξ‖ₑ) :=
    (𝓕 f).continuous.enorm.measurable.aemeasurable
  calc _ ≤ ∫⁻ ξ, ‖lowP ξ * 𝓕 (∂_{eb k} f) ξ‖ₑ := enorm_integral_char_le _ x
    _ ≤ ∫⁻ ξ, ((fun ξ => ENNReal.ofReal (4 * π * ρ ξ)) * fun ξ => ‖𝓕 f ξ‖ₑ) ξ :=
        lintegral_mono fun ξ => low_pt f k ξ
    _ ≤ _ := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two hm1 hm2
    _ = _ := by rw [lintegral_fourier_sq]; rfl


/-! ## High-frequency piece: decays like `2^{-N/4}` against `‖(1-Δ)G‖₂` -/

open scoped Laplacian

/-- `K_high = ∫ √‖ξ‖ w(ξ)⁻²`. -/
def Kh : ℝ≥0∞ := ∫⁻ ξ : E3, ENNReal.ofReal (Real.sqrt ‖ξ‖ * (w ξ)⁻¹ ^ 2)

lemma Kh_ne_top : Kh ≠ ⊤ := by
  have hint : Integrable (fun ξ : E3 => 4 * (1 + ‖ξ‖) ^ (-(7 / 2 : ℝ))) :=
    (integrable_one_add_norm (by simp; norm_num)).const_mul _
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun ξ => ?_) hint.lintegral_lt_top)
  have hw := w_pos ξ
  have hn : 0 < 1 + ‖ξ‖ := by positivity
  have hpi : (1 : ℝ) ≤ (2 * π) ^ 2 := by nlinarith [Real.two_le_pi]
  have h1 : (1 + ‖ξ‖) ^ 2 ≤ 2 * w ξ := by
    unfold w; nlinarith [norm_nonneg ξ, sq_nonneg (‖ξ‖ - 1), mul_le_mul_of_nonneg_right hpi
      (sq_nonneg ‖ξ‖)]
  have h2 : (1 + ‖ξ‖) ^ 4 / 4 ≤ w ξ ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) h1 2
    nlinarith
  have h3 : (w ξ)⁻¹ ^ 2 ≤ 4 * ((1 + ‖ξ‖) ^ 4)⁻¹ := by
    rw [inv_pow]
    calc (w ξ ^ 2)⁻¹ ≤ ((1 + ‖ξ‖) ^ 4 / 4)⁻¹ := inv_anti₀ (by positivity) h2
      _ = _ := by field_simp
  have hs : Real.sqrt ‖ξ‖ ≤ (1 + ‖ξ‖) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]; exact Real.sqrt_le_sqrt (by linarith)
  have he : (1 + ‖ξ‖) ^ (1 / 2 : ℝ) * ((1 + ‖ξ‖) ^ 4)⁻¹ = (1 + ‖ξ‖) ^ (-(7 / 2 : ℝ)) := by
    rw [show (-(7 / 2 : ℝ)) = 1 / 2 + (-4 : ℝ) by norm_num, Real.rpow_add hn,
      Real.rpow_neg hn.le, show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  refine ENNReal.ofReal_le_ofReal ?_
  calc Real.sqrt ‖ξ‖ * (w ξ)⁻¹ ^ 2 ≤ (1 + ‖ξ‖) ^ (1 / 2 : ℝ) * (4 * ((1 + ‖ξ‖) ^ 4)⁻¹) :=
        mul_le_mul hs h3 (by positivity) (by positivity)
    _ = 4 * (1 + ‖ξ‖) ^ (-(7 / 2 : ℝ)) := by rw [← he]; ring

lemma high_coef_sq_le (N : ℕ) (ξ : E3) :
    (‖highP N ξ‖ * (w ξ)⁻¹) ^ 2 ≤ (Real.sqrt ((2 : ℝ) ^ N))⁻¹ * (Real.sqrt ‖ξ‖ * (w ξ)⁻¹ ^ 2) := by
  have hR : (0 : ℝ) < 2 ^ N := by positivity
  have hsR : 0 < Real.sqrt ((2 : ℝ) ^ N) := Real.sqrt_pos.2 hR
  have hw := (inv_pos.2 (w_pos ξ)).le
  by_cases hξ : ‖ξ‖ ≤ 2 ^ N
  · have : ρ (((2 : ℝ) ^ N)⁻¹ • ξ) = 1 := ρ_eq_one (by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR)]
      exact (inv_mul_le_one₀ hR).2 hξ)
    simp only [highP, this, sub_self, Complex.ofReal_zero, norm_zero, zero_mul]
    norm_num; positivity
  · push Not at hξ
    have h1 : ‖highP N ξ‖ ≤ 1 := norm_highP_le N ξ
    have h2 : 1 ≤ (Real.sqrt ((2 : ℝ) ^ N))⁻¹ * Real.sqrt ‖ξ‖ := by
      rw [inv_mul_eq_div, le_div_iff₀ hsR, one_mul]
      exact Real.sqrt_le_sqrt hξ.le
    have h3 : (‖highP N ξ‖ * (w ξ)⁻¹) ^ 2 ≤ ((w ξ)⁻¹) ^ 2 := by
      rw [mul_pow]
      have : ‖highP N ξ‖ ^ 2 ≤ 1 := by
        have := norm_nonneg (highP N ξ); nlinarith
      nlinarith [sq_nonneg (w ξ)⁻¹]
    calc _ ≤ ((w ξ)⁻¹) ^ 2 := h3
      _ ≤ ((Real.sqrt ((2 : ℝ) ^ N))⁻¹ * Real.sqrt ‖ξ‖) * ((w ξ)⁻¹) ^ 2 :=
          le_mul_of_one_le_left (by positivity) h2
      _ = _ := by ring

/-- **High-frequency bound**: `|high| ≤ (2^{-N/2} K_h)^{1/2} ‖G - ΔG‖₂`. -/
lemma high_le (G : 𝓢(E3, ℂ)) (N : ℕ) (x : E3) :
    ‖∫ ξ, 𝐞 (⟪ξ, x⟫_ℝ) • (highP N ξ * 𝓕 G ξ)‖ₑ ≤
      (ENNReal.ofReal (Real.sqrt ((2 : ℝ) ^ N))⁻¹ * Kh) ^ (1 / 2 : ℝ) *
        (∫⁻ y, ‖(G - Δ G) y‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  set a : E3 → ℝ := fun ξ => ‖highP N ξ‖ * (w ξ)⁻¹
  have ha : ∀ ξ, 0 ≤ a ξ := fun ξ => mul_nonneg (norm_nonneg _) (inv_pos.2 (w_pos ξ)).le
  have hpt : ∀ ξ, ‖highP N ξ * 𝓕 G ξ‖ₑ = ENNReal.ofReal (a ξ) * ‖𝓕 (G - Δ G) ξ‖ₑ := by
    intro ξ
    rw [fourier_sub_laplacian, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
      ← ENNReal.ofReal_mul (ha ξ)]
    congr 1
    simp only [a, norm_mul, Complex.norm_real, Real.norm_of_nonneg (w_pos ξ).le]
    field_simp [(w_pos ξ).ne']
  have hm1 : AEMeasurable (fun ξ : E3 => ENNReal.ofReal (a ξ)) := by
    have : Continuous w := by unfold w; fun_prop
    have h2 := continuous_highP N
    exact (ENNReal.measurable_ofReal.comp (h2.norm.mul
      (this.inv₀ fun ξ => (w_pos ξ).ne')).measurable).aemeasurable
  have hm2 : AEMeasurable (fun ξ => ‖𝓕 (G - Δ G) ξ‖ₑ) :=
    (𝓕 (G - Δ G)).continuous.enorm.measurable.aemeasurable
  have hsq : (∫⁻ ξ, ENNReal.ofReal (a ξ) ^ (2 : ℝ)) ≤
      ENNReal.ofReal (Real.sqrt ((2 : ℝ) ^ N))⁻¹ * Kh := by
    unfold Kh
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun ξ => ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (ha ξ) (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := high_coef_sq_le N ξ
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact this
  calc _ ≤ ∫⁻ ξ, ‖highP N ξ * 𝓕 G ξ‖ₑ := enorm_integral_char_le _ x
    _ = ∫⁻ ξ, ((fun ξ => ENNReal.ofReal (a ξ)) * fun ξ => ‖𝓕 (G - Δ G) ξ‖ₑ) ξ :=
        lintegral_congr fun ξ => hpt ξ
    _ ≤ _ := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two hm1 hm2
    _ ≤ _ := by
        rw [lintegral_fourier_sq]
        gcongr

end LogBound
