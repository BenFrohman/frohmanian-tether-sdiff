import Scratch.IBPWholeSpace
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-! # Whole-space vanishing of `∫ div F`

If `F : ℝ³ → ℝ³` is `C¹` and both `F` and `div F` are integrable, then
`∫ div F = 0`. The compactly-supported case is integration by parts
against a cutoff that is identically `1` on a neighbourhood of the
support (`IBPWholeSpace.integral_partial_mul`). The general case
localizes with a radial cutoff `χ_R` and passes to the limit `R → ∞`.

Nothing in this file is a `sorry`, a custom axiom, or an `opaque` trick.
-/

open MeasureTheory Real Filter Topology Set
open scoped ContDiff InnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section
namespace DivergenceWholeSpace

open IBPWholeSpace
open NavierStokes3D (T3 VelocityField div div_smul_field)

/-! ## Radial cutoff `χ_R(x) = ρ(x/R)` -/

/-- A fixed bump: `1` on the unit ball, supported in the ball of radius `2`. -/
def unitBump : ContDiffBump (0 : T3) := ⟨1, 2, one_pos, one_lt_two⟩

/-- Spatial cutoff `χ_R(x) = ρ(x/R)`. -/
def cutoff (R : ℝ) : T3 → ℝ := fun x => (unitBump : T3 → ℝ) (R⁻¹ • x)

lemma contDiff_unitBump : ContDiff ℝ ∞ (unitBump : T3 → ℝ) :=
  unitBump.contDiff

lemma hasCompactSupport_unitBump : HasCompactSupport (unitBump : T3 → ℝ) :=
  unitBump.hasCompactSupport

lemma contDiff_cutoff {R : ℝ} : ContDiff ℝ ∞ (cutoff R) :=
  contDiff_unitBump.comp (contDiff_id.const_smul R⁻¹)

lemma hasCompactSupport_cutoff {R : ℝ} (hR : R ≠ 0) :
    HasCompactSupport (cutoff R) :=
  hasCompactSupport_unitBump.comp_smul (inv_ne_zero hR)

lemma cutoff_nonneg {R : ℝ} (x : T3) : 0 ≤ cutoff R x :=
  unitBump.nonneg

lemma cutoff_le_one {R : ℝ} (x : T3) : cutoff R x ≤ 1 :=
  unitBump.le_one

lemma abs_cutoff_le_one {R : ℝ} (x : T3) : |cutoff R x| ≤ 1 :=
  abs_le.mpr ⟨le_trans (by norm_num : (-1 : ℝ) ≤ 0) (cutoff_nonneg x), cutoff_le_one x⟩

/-- `χ_R ≡ 1` on the closed ball of radius `R`, for `R > 0`. -/
lemma cutoff_eq_one_of_le {R : ℝ} (hR : 0 < R) {x : T3} (hx : ‖x‖ ≤ R) :
    cutoff R x = 1 := by
  apply unitBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hR)]
  have : R⁻¹ * ‖x‖ ≤ 1 := (inv_mul_le_iff₀ hR).mpr (by simpa using hx)
  simpa [unitBump] using this

lemma fderiv_cutoff {R : ℝ} (x : T3) :
    fderiv ℝ (cutoff R) x =
      R⁻¹ • fderiv ℝ (fun z => (unitBump : T3 → ℝ) z) (R⁻¹ • x) := by
  simpa [cutoff] using
    (fderiv_comp_smul (f := fun z => (unitBump : T3 → ℝ) z) (x := x) R⁻¹)

/-- First derivatives of the fixed bump are globally bounded. -/
lemma exists_bound_unitBump_fderiv :
    ∃ K, 0 ≤ K ∧ ∀ y, ‖fderiv ℝ (fun z => (unitBump : T3 → ℝ) z) y‖ ≤ K := by
  have hc := hasCompactSupport_unitBump
  have hcont : Continuous (fderiv ℝ (fun z => (unitBump : T3 → ℝ) z)) :=
    (contDiff_unitBump.continuous_fderiv (n := ∞) (by simp))
  have hdc : HasCompactSupport (fderiv ℝ (fun z => (unitBump : T3 → ℝ) z)) :=
    HasCompactSupport.fderiv (𝕜 := ℝ) hc
  obtain ⟨K, hK⟩ := hcont.bounded_above_of_compact_support hdc
  exact ⟨K, (norm_nonneg _).trans (hK 0), hK⟩

lemma differentiableAt_cutoff {R : ℝ} (x : T3) :
    DifferentiableAt ℝ (cutoff R) x :=
  (contDiff_cutoff (R := R)).differentiable (by simp) x

lemma contDiff_one_cutoff {R : ℝ} : ContDiff ℝ 1 (cutoff R) :=
  (contDiff_cutoff (R := R)).of_le (by exact_mod_cast le_top)

/-- On the open ball of radius `R`, `χ_R` is locally constant, so `∇χ_R = 0`. -/
lemma gradient_cutoff_eq_zero_of_lt {R : ℝ} (hR : 0 < R) {x : T3}
    (hx : ‖x‖ < R) : gradient (cutoff R) x = 0 := by
  have hball : cutoff R =ᶠ[𝓝 x] fun _ : T3 => (1 : ℝ) := by
    have : Metric.ball (0 : T3) R ∈ 𝓝 x :=
      Metric.isOpen_ball.mem_nhds
        (by simpa [Metric.mem_ball, dist_zero_right] using hx)
    filter_upwards [this] with y hy
    exact cutoff_eq_one_of_le hR
      (le_of_lt (by simpa [Metric.mem_ball, dist_zero_right] using hy))
  have hf0 : HasFDerivAt (cutoff R) (0 : T3 →L[ℝ] ℝ) x :=
    (hasFDerivAt_const (1 : ℝ) x).congr_of_eventuallyEq hball
  apply ext_inner_right (𝕜 := ℝ)
  intro v
  rw [inner_gradient_left (differentiableAt_cutoff x), hf0.fderiv,
    ContinuousLinearMap.zero_apply, inner_zero_left]

lemma abs_inner_gradient_cutoff_le {R K : ℝ}
    (hK : ∀ y, ‖fderiv ℝ (fun z => (unitBump : T3 → ℝ) z) y‖ ≤ K)
    (F : VelocityField) (x : T3) :
    |inner ℝ (gradient (cutoff R) x) (F x)| ≤ |R⁻¹| * K * ‖F x‖ := by
  have hinner :
      inner ℝ (gradient (cutoff R) x) (F x) =
        fderiv ℝ (cutoff R) x (F x) :=
    inner_gradient_left (differentiableAt_cutoff x) (y := F x)
  rw [hinner]
  have hop : |fderiv ℝ (cutoff R) x (F x)| ≤
      ‖fderiv ℝ (cutoff R) x‖ * ‖F x‖ :=
    (fderiv ℝ (cutoff R) x).le_opNorm (F x)
  have hfd : ‖fderiv ℝ (cutoff R) x‖ ≤ |R⁻¹| * K := by
    rw [fderiv_cutoff, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hK _) (abs_nonneg _)
  exact hop.trans (mul_le_mul_of_nonneg_right hfd (norm_nonneg _))

/-! ## Compactly supported case -/

lemma hasCompactSupport_coord {F : VelocityField} (h : HasCompactSupport F) (i : Fin 3) :
    HasCompactSupport (fun x => F x i) :=
  h.comp_left (g := fun v : T3 => v i) (by simp)

lemma integrable_cs {f : T3 → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable f volume :=
  hf.integrable_of_hasCompactSupport hc

lemma integrable_mul_cs {f g : T3 → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hc : HasCompactSupport g) :
    Integrable (fun x => f x * g x) volume :=
  integrable_cs (hf.mul hg) (hc.mul_left)

def coordCLM (i : Fin 3) : T3 →L[ℝ] ℝ :=
  PiLp.proj (p := (2 : ENNReal)) (fun _ : Fin 3 => ℝ) i

lemma coordCLM_apply (i : Fin 3) (x : T3) : coordCLM i x = x i := rfl

lemma contDiff_coord {F : VelocityField} (hF : ContDiff ℝ 1 F) (i : Fin 3) :
    ContDiff ℝ 1 (fun x => F x i) := by
  have hfun : (fun x => F x i) = coordCLM i ∘ F :=
    funext fun x => (coordCLM_apply i (F x)).symm
  rw [hfun]
  exact ((coordCLM i).contDiff.of_le (by exact_mod_cast le_top)).comp hF

lemma eq_zero_of_notMem_tsupport {E : Type*} [Zero E] {f : T3 → E} {x : T3}
    (hx : x ∉ tsupport f) : f x = 0 :=
  notMem_tsupport_iff_eventuallyEq.mp hx |>.eq_of_nhds

lemma div_eq_zero_of_notMem_tsupport {F : VelocityField} {x : T3}
    (hx : x ∉ tsupport F) : div F x = 0 := by
  have hzero : ∀ᶠ y in 𝓝 x, F y = 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hx
  have hfun : ∀ i, (fun y => F y i) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := fun i => by
    filter_upwards [hzero] with y hy
    simp [hy]
  have hfd : ∀ i, fderiv ℝ (fun y => F y i) x = 0 := fun i =>
    ((hasFDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq (hfun i)).fderiv
  unfold div
  simp [hfd]

lemma continuous_div_of_contDiff {F : VelocityField} (hF : ContDiff ℝ 1 F) :
    Continuous (div F) := by
  have hcoord : ∀ i, Continuous fun x =>
      (fderiv ℝ (fun y => F y i) x) (e i) := fun i =>
    ((contDiff_coord hF i).continuous_fderiv (by simp)).clm_apply continuous_const
  exact continuous_finset_sum _ fun i _ => hcoord i

lemma continuous_partial_coord {F : VelocityField} (hF : ContDiff ℝ 1 F) (i : Fin 3) :
    Continuous fun x => fderiv ℝ (fun y => F y i) x (e i) :=
  ((contDiff_coord hF i).continuous_fderiv (by simp)).clm_apply continuous_const

/-- If `F` is `C¹` and compactly supported, then `∫ div F = 0`. -/
theorem integral_div_eq_zero_of_hasCompactSupport
    (F : VelocityField) (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F) :
    ∫ x, div F x ∂volume = 0 := by
  have hbdd : Bornology.IsBounded (tsupport F) := hc.isBounded
  obtain ⟨r, hrpos, hsub⟩ := hbdd.subset_closedBall_lt (0 : ℝ) (0 : T3)
  set R : ℝ := r + 1
  have hR : 0 < R := add_pos_of_pos_of_nonneg hrpos zero_le_one
  have hRne : R ≠ 0 := ne_of_gt hR
  have hsubR : tsupport F ⊆ Metric.ball (0 : T3) R := by
    intro x hx
    have : ‖x‖ ≤ r := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hsub hx
    have : ‖x‖ < R := this.trans_lt (lt_add_of_pos_right r zero_lt_one)
    simpa [Metric.mem_ball, dist_zero_right] using this
  have hψ : ContDiff ℝ 1 (cutoff R) := contDiff_one_cutoff
  have hψc : HasCompactSupport (cutoff R) := hasCompactSupport_cutoff hRne
  have hintL : ∀ i, Integrable
      (fun x => fderiv ℝ (fun y => F y i) x (e i) * cutoff R x) volume := fun i =>
    integrable_mul_cs (continuous_partial_coord hF i) hψ.continuous hψc
  have hintR' : ∀ i, Integrable
      (fun x => F x i * fderiv ℝ (cutoff R) x (e i)) volume := fun i =>
    integrable_mul_cs (contDiff_coord hF i).continuous
      ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (HasCompactSupport.fderiv_apply (𝕜 := ℝ) (E := T3) (F := ℝ) hψc (e i))
  have hintP : ∀ i, Integrable (fun x => F x i * cutoff R x) volume := fun i =>
    integrable_mul_cs (contDiff_coord hF i).continuous hψ.continuous hψc
  have hibp : ∀ i,
      ∫ x, fderiv ℝ (fun y => F y i) x (e i) * cutoff R x ∂volume =
        -∫ x, F x i * fderiv ℝ (cutoff R) x (e i) ∂volume := fun i =>
    integral_partial_mul_of_contDiff i (contDiff_coord hF i) hψ
      (hintL i) (hintR' i) (hintP i)
  have hdivχ :
      (fun x => div F x * cutoff R x) =
        fun x => ∑ i : Fin 3,
          fderiv ℝ (fun y => F y i) x (e i) * cutoff R x := by
    funext x
    unfold div
    rw [Finset.sum_mul]
    rfl
  have hinter :
      (fun x => inner ℝ (gradient (cutoff R) x) (F x)) =
        fun x => ∑ i : Fin 3,
          F x i * fderiv ℝ (cutoff R) x (e i) := by
    funext x
    have hdiff := differentiableAt_cutoff (R := R) x
    have h1 : inner ℝ (gradient (cutoff R) x) (F x) =
        fderiv ℝ (cutoff R) x (F x) :=
      inner_gradient_left hdiff (y := F x)
    have h2 : fderiv ℝ (cutoff R) x (F x) =
        ∑ i : Fin 3, F x i * fderiv ℝ (cutoff R) x (e i) := by
      have hFsum : F x = ∑ i : Fin 3, F x i • e i := by
        ext k
        simp [e, EuclideanSpace.single, Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [hFsum]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
    exact h1.trans h2
  have hsumL :=
    integral_finset_sum (μ := volume) (s := (Finset.univ : Finset (Fin 3)))
      (fun i _ => hintL i)
  have hsumR :=
    integral_finset_sum (μ := volume) (s := (Finset.univ : Finset (Fin 3)))
      (fun i _ => hintR' i)
  have hleft :
      ∫ x, div F x * cutoff R x ∂volume =
        ∑ i : Fin 3, ∫ x, fderiv ℝ (fun y => F y i) x (e i) * cutoff R x ∂volume := by
    rw [hdivχ]
    exact hsumL
  have hright :
      ∫ x, inner ℝ (gradient (cutoff R) x) (F x) ∂volume =
        ∑ i : Fin 3, ∫ x, F x i * fderiv ℝ (cutoff R) x (e i) ∂volume := by
    rw [hinter]
    exact hsumR
  have hIBPsum :
      ∫ x, div F x * cutoff R x ∂volume =
        -∫ x, inner ℝ (gradient (cutoff R) x) (F x) ∂volume := by
    rw [hleft, hright, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => hibp i
  have hχ1' : ∀ x, div F x * cutoff R x = div F x := fun x => by
    by_cases hx : x ∈ tsupport F
    · have hx1 : cutoff R x = 1 :=
        cutoff_eq_one_of_le hR (le_of_lt (by
          simpa [Metric.mem_ball, dist_zero_right] using hsubR hx))
      rw [hx1, mul_one]
    · have : div F x = 0 := div_eq_zero_of_notMem_tsupport hx
      simp [this]
  have hgrad0 : ∀ x, inner ℝ (gradient (cutoff R) x) (F x) = 0 := fun x => by
    by_cases hx : x ∈ tsupport F
    · have hg : gradient (cutoff R) x = 0 :=
        gradient_cutoff_eq_zero_of_lt hR (by
          simpa [Metric.mem_ball, dist_zero_right] using hsubR hx)
      simp [hg]
    · have : F x = 0 := eq_zero_of_notMem_tsupport hx
      simp [this]
  have hL : ∫ x, div F x * cutoff R x ∂volume = ∫ x, div F x ∂volume :=
    integral_congr_ae (Filter.Eventually.of_forall hχ1')
  have hR0 : ∫ x, inner ℝ (gradient (cutoff R) x) (F x) ∂volume = 0 := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hgrad0), integral_zero]
  rw [hL, hR0, neg_zero] at hIBPsum
  exact hIBPsum

/-! ## The general integrable case -/

lemma hasCompactSupport_cutoff_smul {R : ℝ} (hR : R ≠ 0) (F : VelocityField) :
    HasCompactSupport (fun y => cutoff R y • F y) :=
  (hasCompactSupport_cutoff hR).smul_right

lemma contDiff_cutoff_smul {R : ℝ} {F : VelocityField} (hF : ContDiff ℝ 1 F) :
    ContDiff ℝ 1 (fun y => cutoff R y • F y) :=
  (contDiff_one_cutoff).smul hF

lemma div_cutoff_smul {R : ℝ} (F : VelocityField) (hF : ContDiff ℝ 1 F) (x : T3) :
    div (fun y => cutoff R y • F y) x =
      inner ℝ (gradient (cutoff R) x) (F x) + cutoff R x * div F x :=
  div_smul_field (cutoff R) F x (differentiableAt_cutoff x)
    (fun i => (contDiff_coord hF i).differentiable (by simp) x)

/-- **Whole-space vanishing flux.** If `F` is `C¹` and both `F` and `div F`
are integrable on ℝ³, then `∫ div F = 0`. -/
theorem integral_div_eq_zero
    (F : VelocityField) (hF : ContDiff ℝ 1 F)
    (hF1 : Integrable F volume) (hdiv : Integrable (div F) volume) :
    ∫ x, div F x ∂volume = 0 := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_unitBump_fderiv
  have hloc : ∀ n : ℕ,
      ∫ x, div (fun y => cutoff (n + 1 : ℝ) y • F y) x ∂volume = 0 := fun n =>
    integral_div_eq_zero_of_hasCompactSupport _
      (contDiff_cutoff_smul hF)
      (hasCompactSupport_cutoff_smul (Nat.cast_add_one_ne_zero n) F)
  have hid : ∀ n : ℕ,
      ∫ x, inner ℝ (gradient (cutoff (n + 1 : ℝ)) x) (F x) +
          cutoff (n + 1 : ℝ) x * div F x ∂volume = 0 := fun n => by
    have hfun :
        (fun x => div (fun y => cutoff (n + 1 : ℝ) y • F y) x) =
          fun x => inner ℝ (gradient (cutoff (n + 1 : ℝ)) x) (F x) +
            cutoff (n + 1 : ℝ) x * div F x := by
      funext x
      exact div_cutoff_smul F hF x
    simpa [hfun] using hloc n
  have hintχ : ∀ n : ℕ,
      Integrable (fun x => cutoff (n + 1 : ℝ) x * div F x) volume := fun n =>
    hdiv.bdd_mul
      (contDiff_one_cutoff (R := (n + 1 : ℝ))).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using abs_cutoff_le_one (R := (n + 1 : ℝ)) x)
  have hintGrad : ∀ n : ℕ,
      Integrable (fun x => inner ℝ (gradient (cutoff (n + 1 : ℝ)) x) (F x))
        volume := fun n => by
    have hbound : ∀ x,
        ‖inner ℝ (gradient (cutoff (n + 1 : ℝ)) x) (F x)‖ ≤
          K * ‖F x‖ := fun x => by
      have h1 := abs_inner_gradient_cutoff_le (R := (n + 1 : ℝ)) hK F x
      have hinv : |(n + 1 : ℝ)⁻¹| ≤ 1 := by
        have hpos : 0 < (n + 1 : ℝ) := Nat.cast_add_one_pos n
        rw [abs_inv, abs_of_pos hpos]
        exact inv_le_one_of_one_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg n))
      have : |(n + 1 : ℝ)⁻¹| * K * ‖F x‖ ≤ 1 * K * ‖F x‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hinv hK0) (norm_nonneg _)
      simpa [Real.norm_eq_abs, one_mul] using h1.trans this
    have hcont : Continuous fun x =>
        inner ℝ (gradient (cutoff (n + 1 : ℝ)) x) (F x) := by
      have hfun :
          (fun x => inner ℝ (gradient (cutoff (n + 1 : ℝ)) x) (F x)) =
            fun x => fderiv ℝ (cutoff (n + 1 : ℝ)) x (F x) := by
        funext x
        exact inner_gradient_left (differentiableAt_cutoff x) (y := F x)
      rw [hfun]
      exact ((contDiff_one_cutoff (R := (n + 1 : ℝ))).continuous_fderiv
        (by simp)).clm_apply hF.continuous
    exact (hF1.norm.const_mul K).mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  have hsum : ∀ n : ℕ,
      (∫ x, inner ℝ (gradient (cutoff (n + 1 : ℝ)) x) (F x) ∂volume) +
        ∫ x, cutoff (n + 1 : ℝ) x * div F x ∂volume = 0 := fun n =>
    (integral_add (hintGrad n) (hintχ n)).symm.trans (hid n)
  have hχlim :
      Tendsto (fun n : ℕ => ∫ x, cutoff (n + 1 : ℝ) x * div F x ∂volume)
        atTop (nhds (∫ x, div F x ∂volume)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => |div F x|) (fun n => (hintχ n).aestronglyMeasurable)
      hdiv.norm ?_ ?_
    · intro n
      refine Filter.Eventually.of_forall fun x => ?_
      have : |cutoff (n + 1 : ℝ) x * div F x| ≤ |div F x| := by
        rw [abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) (abs_cutoff_le_one _)
      simpa [Real.norm_eq_abs] using this
    · refine Filter.Eventually.of_forall fun x => ?_
      have h1 : ∀ᶠ n : ℕ in atTop, cutoff (n + 1 : ℝ) x = 1 := by
        rw [eventually_atTop]
        refine ⟨Nat.ceil ‖x‖, fun n hn => ?_⟩
        have : ‖x‖ ≤ n :=
          (Nat.le_ceil ‖x‖).trans (Nat.cast_le.mpr hn)
        exact cutoff_eq_one_of_le (by exact_mod_cast Nat.succ_pos n)
          (this.trans (by exact_mod_cast Nat.le_succ n))
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [h1] with n hn
      rw [hn, one_mul]
  have hgradLim :
      Tendsto (fun n : ℕ =>
          ∫ x, inner ℝ (gradient (cutoff (n + 1 : ℝ)) x) (F x) ∂volume)
        atTop (nhds 0) := by
    have h0 : (∫ x : T3, (0 : ℝ) ∂volume) = 0 :=
      integral_zero (α := T3) (G := ℝ) (μ := volume)
    rw [← h0]
    refine tendsto_integral_of_dominated_convergence
      (fun x => K * ‖F x‖) (fun n => (hintGrad n).aestronglyMeasurable)
      (hF1.norm.const_mul K) ?_ ?_
    · intro n
      refine Filter.Eventually.of_forall fun x => ?_
      have h1 := abs_inner_gradient_cutoff_le (R := (n + 1 : ℝ)) hK F x
      have hinv : |(n + 1 : ℝ)⁻¹| ≤ 1 := by
        have hpos : 0 < (n + 1 : ℝ) := Nat.cast_add_one_pos n
        rw [abs_inv, abs_of_pos hpos]
        exact inv_le_one_of_one_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg n))
      have : |(n + 1 : ℝ)⁻¹| * K * ‖F x‖ ≤ 1 * K * ‖F x‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hinv hK0) (norm_nonneg _)
      simpa [Real.norm_eq_abs, one_mul] using h1.trans this
    · refine Filter.Eventually.of_forall fun x => ?_
      have h0pt : ∀ᶠ n : ℕ in atTop, gradient (cutoff (n + 1 : ℝ)) x = 0 := by
        rw [eventually_atTop]
        refine ⟨Nat.ceil (‖x‖ + 1), fun n hn => ?_⟩
        have hle : ‖x‖ + 1 ≤ n :=
          (Nat.le_ceil (‖x‖ + 1)).trans (Nat.cast_le.mpr hn)
        have : ‖x‖ < (n + 1 : ℝ) := by linarith
        exact gradient_cutoff_eq_zero_of_lt (by exact_mod_cast Nat.succ_pos n) this
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [h0pt] with n hn
      simp [hn]
  have hneg : Tendsto
      (fun n : ℕ => -∫ x, inner ℝ (gradient (cutoff (n + 1 : ℝ)) x) (F x) ∂volume)
      atTop (nhds 0) := by
    simpa using hgradLim.neg
  have hχeq : (fun n : ℕ => ∫ x, cutoff (n + 1 : ℝ) x * div F x ∂volume) =
      fun n : ℕ => -∫ x, inner ℝ (gradient (cutoff (n + 1 : ℝ)) x) (F x) ∂volume := by
    funext n
    linarith [hsum n]
  have hχlim0 : Tendsto
      (fun n : ℕ => ∫ x, cutoff (n + 1 : ℝ) x * div F x ∂volume) atTop (nhds 0) := by
    rw [hχeq]
    exact hneg
  exact tendsto_nhds_unique hχlim hχlim0

#print axioms DivergenceWholeSpace.integral_div_eq_zero_of_hasCompactSupport
#print axioms DivergenceWholeSpace.integral_div_eq_zero

end DivergenceWholeSpace
