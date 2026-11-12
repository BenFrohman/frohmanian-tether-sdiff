import Scratch.KatoPonce
import Scratch.IBPWholeSpace
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Data.Real.ConjExponents
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Scratch.FourierCutoff

/-! # The H³ Kato commutator estimate

This file proves (or, where a remaining analytic input is still named, reduces)
`KatoPonce.H3CommutatorEstimate`: there is `C ≥ 0` such that for every
`C^∞` field with finite H³ energy,

`|∑_{|α|≤3} ∫ ⟨∂^α u, [∂^α, u·∇]u⟩| ≤ C ‖∇u‖_∞ ‖u‖²_{H³}`.

What is proved here: the first-order Leibniz identification
`[∂ᵢ, u·∇]u = (∂ᵢ u)·∇u` (including the `ContDiff 2 ≤ ∞` unification), the
pointwise bound `‖[∂ᵢ, u·∇]u‖ ≤ ‖∇u‖ ‖∂ᵢ u‖`, the integral pairing bound
`|∫ ⟨∂ᵢ u, [∂ᵢ, u·∇]u⟩| ≤ ‖∇u‖_∞ ∫ |∂ᵢ u|²`, the compact-support
Gagliardo–Nirenberg bound `∫ |∇φ|⁴ ≤ (√3+2)² M² ∫ |Hess φ|²`, and the
general estimate `H3GagliardoNirenberg` for every `C^∞` field with
finite H³ energy. The latter is obtained by applying the compact-support
identity to the cutoffs `χ_R φ`, bounding `∫ |Hess(χ_R φ)|²` uniformly
by the H² energy of `φ` for `R ≥ 1`, and passing to the limit by Fatou.
Direct IBP on `φ` itself is not available: `|∇φ|⁴` is not a priori
integrable from finite H² energy plus a sup bound. The order-zero
commutator is already `convectiveCommutator_zero` in `KatoPonce`.

What remains for `H3CommutatorEstimate` itself: the Leibniz expansion
and Hölder bounds for `|α| = 2, 3` (the `|α| = 3`, `|β| = 2` term is the
one that needs GN), and the assembly. A Fourier-side product estimate
would bound by `‖û‖` norms, which do not imply the `‖∇u‖_∞` form, so it
is not used here. (`GradBound` already gives `‖∇u‖_∞ ≲ ‖u‖_{H³}` and
`BddAbove`, which we do use.)

The statement of `H3CommutatorEstimate` is not weakened; it remains a
named `Prop` in `KatoPonce.lean`, and `katoPonce_h3_energy` still takes
it as a hypothesis.

Nothing in this file is a `sorry`, a custom axiom, or an `opaque` trick.
-/

open MeasureTheory hiding volume
open NavierStokes3D FrohmanianTether Set
open scoped ContDiff InnerProductSpace

set_option autoImplicit false

noncomputable section
namespace KatoPonceCommutator

open KatoPonce R3BKM GradBound

/-! ## Preliminaries -/

lemma wordDeriv_succ {k : ℕ} (α : Fin (k + 1) → Fin 3) {f : VelocityField}
    (hf : ContDiff ℝ ∞ f) :
    wordDeriv (k + 1) α f =
      fun x => fderiv ℝ (wordDeriv k (Fin.tail α) f) x
        (EuclideanSpace.single (α 0) (1 : ℝ)) := by
  funext x
  simp only [wordDeriv]
  rw [iteratedFDeriv_succ_apply_left]
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) x :=
    (hf.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)) x
  show _ = fderiv ℝ (fun y => iteratedFDeriv ℝ k f y
      (fun j => EuclideanSpace.single (Fin.tail α j) (1 : ℝ))) x _
  rw [fderiv_continuousMultilinear_apply_const_apply hd]
  rfl

lemma le_gradSup {u : VelocityField} (hu : ContDiff ℝ ∞ u)
    (hE : sobolevEnergy 3 u < ⊤) (x : T3) :
    ‖fderiv ℝ u x‖ ≤ gradSup u :=
  le_ciSup (bddAbove_grad_slice hu hE) x

lemma lintegral_wordDeriv_sq_le (m : ℕ) (f : VelocityField) {k : ℕ}
    (hk : k ≤ m) (α : Fin k → Fin 3) :
    ∫⁻ x, ‖wordDeriv k α f x‖ₑ ^ 2 ≤ sobolevEnergy m f := by
  have hmem : k ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
  have hterm :
      ∫⁻ x, ‖wordDeriv k α f x‖ₑ ^ 2 ≤
        ∑ β : Fin k → Fin 3, ∫⁻ x, ‖wordDeriv k β f x‖ₑ ^ 2 :=
    Finset.single_le_sum
      (f := fun β : Fin k → Fin 3 => ∫⁻ x, ‖wordDeriv k β f x‖ₑ ^ 2)
      (fun _ _ => zero_le _) (Finset.mem_univ α)
  unfold sobolevEnergy
  refine hterm.trans ?_
  exact Finset.single_le_sum
    (f := fun i : ℕ => ∑ β : Fin i → Fin 3,
      ∫⁻ x, ‖iteratedFDeriv ℝ i f x (fun j => EuclideanSpace.single (β j) (1 : ℝ))‖ₑ ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => zero_le _) hmem

lemma differentiable_of_infty {f : VelocityField} (hf : ContDiff ℝ ∞ f) :
    Differentiable ℝ f :=
  hf.differentiable (by simp)

lemma differentiable_fderiv_of_infty {f : VelocityField} (hf : ContDiff ℝ ∞ f) :
    Differentiable ℝ (fderiv ℝ f) :=
  ((contDiff_of_infty (n := 2) hf).fderiv_right (m := 1)
    (by norm_num)).differentiable_one

/-- The first-order convective commutator is `(∂ᵢ u) · ∇u`. -/
theorem convectiveCommutator_order_one {u : VelocityField}
    (hu : ContDiff ℝ ∞ u) (α : Fin 1 → Fin 3) (x : T3) :
    convectiveCommutator 1 α u x = convective (wordDeriv 1 α u) u x := by
  set e : T3 := EuclideanSpace.single (α 0) (1 : ℝ)
  have huD := differentiable_of_infty hu
  have hDu := differentiable_fderiv_of_infty hu
  have hprod :=
    fderiv_clm_apply (c := fderiv ℝ u) (u := u) (hDu x) (huD x)
  have hwd : wordDeriv 1 α (convective u u) x =
      fderiv ℝ (fun y => (fderiv ℝ u y) (u y)) x e := by
    rw [wordDeriv_one]; rfl
  have hL :
      fderiv ℝ (fun y => (fderiv ℝ u y) e) x (u x) =
        (fderiv ℝ (fderiv ℝ u) x (u x)) e := by
    let L : (T3 →L[ℝ] T3) →L[ℝ] T3 :=
      ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin 3)) e
    have hcomp :
        (fun y => (fderiv ℝ u y) e) = ⇑L ∘ fderiv ℝ u := rfl
    rw [hcomp, fderiv_comp (f := fderiv ℝ u) (g := ⇑L)
      (x := x) L.differentiableAt (hDu x), ContinuousLinearMap.fderiv]
    rfl
  have hsym :
      (fderiv ℝ (fderiv ℝ u) x (u x)) e =
        (fderiv ℝ (fderiv ℝ u) x e) (u x) :=
    second_derivative_symmetric (fun y => (huD y).hasFDerivAt)
      ((hDu x).hasFDerivAt) (u x) e
  have hwd1 : wordDeriv 1 α u = fun y => fderiv ℝ u y e := by
    funext y; exact wordDeriv_one α u y
  have htr : convective u (wordDeriv 1 α u) x =
      (fderiv ℝ (fderiv ℝ u) x (u x)) e := by
    simp only [convective, hwd1]
    exact hL
  calc
    convectiveCommutator 1 α u x
        = wordDeriv 1 α (convective u u) x - convective u (wordDeriv 1 α u) x := rfl
    _ = fderiv ℝ (fun y => (fderiv ℝ u y) (u y)) x e -
          (fderiv ℝ (fderiv ℝ u) x (u x)) e := by
          rw [hwd, htr]
    _ = ((fderiv ℝ u x) (fderiv ℝ u x e) + (fderiv ℝ (fderiv ℝ u) x e) (u x)) -
          (fderiv ℝ (fderiv ℝ u) x (u x)) e := by
          rw [hprod, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
            ContinuousLinearMap.flip_apply]
    _ = (fderiv ℝ u x) (fderiv ℝ u x e) := by
          rw [hsym, sub_eq_add_neg, add_assoc, add_neg_cancel, add_zero]
    _ = convective (wordDeriv 1 α u) u x := by
          simp only [convective, hwd1]

/-- Pointwise bound: `‖[∂ᵢ, u·∇]u‖ ≤ ‖∇u‖ ‖∂ᵢ u‖`. -/
theorem norm_convectiveCommutator_order_one {u : VelocityField}
    (hu : ContDiff ℝ ∞ u) (α : Fin 1 → Fin 3) (x : T3) :
    ‖convectiveCommutator 1 α u x‖ ≤
      ‖fderiv ℝ u x‖ * ‖wordDeriv 1 α u x‖ := by
  rw [convectiveCommutator_order_one hu α x]
  exact convective_norm_le (wordDeriv 1 α u) u x (differentiable_of_infty hu x)

lemma memLp_wordDeriv {f : VelocityField} (hf : ContDiff ℝ ∞ f)
    (hE : sobolevEnergy 3 f < ⊤) {k : ℕ} (hk : k ≤ 3) (α : Fin k → Fin 3) :
    MemLp (wordDeriv k α f) 2 volume := by
  have hmeas : AEStronglyMeasurable (wordDeriv k α f) volume :=
    (contDiff_wordDeriv α hf).continuous.aestronglyMeasurable
  have hlt : ∫⁻ x, ‖wordDeriv k α f x‖ₑ ^ 2 < ⊤ :=
    (lintegral_wordDeriv_sq_le 3 f hk α).trans_lt hE
  refine ⟨hmeas, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp : (2 : ENNReal) ≠ 0)
    ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat]
  have hpow : (fun x => ‖wordDeriv k α f x‖ₑ ^ (2 : ℝ)) =
      fun x => ‖wordDeriv k α f x‖ₑ ^ (2 : ℕ) :=
    funext fun x => ENNReal.rpow_natCast _ 2
  rw [hpow]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hlt.ne

lemma integrable_wordDeriv_sq {f : VelocityField} (hf : ContDiff ℝ ∞ f)
    (hE : sobolevEnergy 3 f < ⊤) {k : ℕ} (hk : k ≤ 3) (α : Fin k → Fin 3) :
    Integrable (fun x => ‖wordDeriv k α f x‖ ^ 2) volume := by
  have h := memLp_wordDeriv hf hE hk α
  have h2 := h.integrable_norm_rpow (by simp : (2 : ENNReal) ≠ 0) ENNReal.ofNat_ne_top
  simpa using h2

/-- Absolute pairing of the first-order commutator is at most
`gradSup u * ∫ ‖∂ᵢ u‖²`. -/
theorem abs_integral_commutator_order_one {u : VelocityField}
    (hu : ContDiff ℝ ∞ u) (hE : sobolevEnergy 3 u < ⊤) (α : Fin 1 → Fin 3) :
    |∫ x, inner ℝ (wordDeriv 1 α u x) (convectiveCommutator 1 α u x) ∂volume| ≤
      gradSup u * ∫ x, ‖wordDeriv 1 α u x‖ ^ 2 ∂volume := by
  have hsq := integrable_wordDeriv_sq hu hE (by norm_num : (1 : ℕ) ≤ 3) α
  have hpt : ∀ x,
      |inner ℝ (wordDeriv 1 α u x) (convectiveCommutator 1 α u x)| ≤
        gradSup u * ‖wordDeriv 1 α u x‖ ^ 2 := by
    intro x
    have hcs := abs_real_inner_le_norm (wordDeriv 1 α u x) (convectiveCommutator 1 α u x)
    have hcomm := norm_convectiveCommutator_order_one hu α x
    have hgs := le_gradSup hu hE x
    have h1 : 0 ≤ ‖wordDeriv 1 α u x‖ := norm_nonneg _
    have h2 : 0 ≤ ‖fderiv ℝ u x‖ := norm_nonneg _
    nlinarith
  have hcont_comm : Continuous (convectiveCommutator 1 α u) := by
    unfold convectiveCommutator
    exact (contDiff_wordDeriv α (contDiff_convective hu hu)).continuous.sub
      (contDiff_convective hu (contDiff_wordDeriv α hu)).continuous
  have hinter : Integrable
      (fun x => inner ℝ (wordDeriv 1 α u x) (convectiveCommutator 1 α u x)) volume := by
    refine (hsq.const_mul (gradSup u)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact ((contDiff_wordDeriv α hu).continuous.inner hcont_comm).aestronglyMeasurable
    · simpa [Real.norm_eq_abs] using hpt x
  have habs :
      |∫ x, inner ℝ (wordDeriv 1 α u x) (convectiveCommutator 1 α u x) ∂volume| ≤
        ∫ x, |inner ℝ (wordDeriv 1 α u x) (convectiveCommutator 1 α u x)| ∂volume := by
    simpa [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm
        (f := fun x => inner ℝ (wordDeriv 1 α u x) (convectiveCommutator 1 α u x)))
  refine habs.trans ?_
  have hnonneg : 0 ≤ᵐ[volume] fun x =>
      |inner ℝ (wordDeriv 1 α u x) (convectiveCommutator 1 α u x)| :=
    Filter.Eventually.of_forall fun _ => abs_nonneg _
  have hmono := integral_mono_of_nonneg hnonneg (hsq.const_mul (gradSup u))
    (Filter.Eventually.of_forall hpt)
  have hfactor :
      ∫ x, gradSup u * ‖wordDeriv 1 α u x‖ ^ 2 ∂volume =
        gradSup u * ∫ x, ‖wordDeriv 1 α u x‖ ^ 2 ∂volume :=
    integral_const_mul (gradSup u) _
  rwa [← hfactor]

/-! ## Gagliardo–Nirenberg via whole-space IBP -/

open IBPWholeSpace (e)

/-- Directional partial `∂ᵢ φ`. -/
def partiali (φ : T3 → ℝ) (i : Fin 3) : T3 → ℝ :=
  fun x => fderiv ℝ φ x (e i)

/-- `|∇φ|²`. -/
def gradNormSq (φ : T3 → ℝ) : T3 → ℝ :=
  fun x => ∑ i : Fin 3, partiali φ i x ^ 2

lemma contDiff_partiali {φ : T3 → ℝ} (hφ : ContDiff ℝ ∞ φ) (i : Fin 3) :
    ContDiff ℝ ∞ (partiali φ i) :=
  (hφ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

lemma contDiff_gradNormSq {φ : T3 → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (gradNormSq φ) :=
  ContDiff.sum fun i _ => (contDiff_partiali hφ i).pow 2

lemma hasCompactSupport_partiali {φ : T3 → ℝ} (hc : HasCompactSupport φ) (i : Fin 3) :
    HasCompactSupport (partiali φ i) :=
  HasCompactSupport.fderiv_apply (𝕜 := ℝ) hc (e i)

lemma hasCompactSupport_sq_partiali {φ : T3 → ℝ} (hc : HasCompactSupport φ) (i : Fin 3) :
    HasCompactSupport (fun x => partiali φ i x ^ 2) := by
  have : (fun x => partiali φ i x ^ 2) = partiali φ i * partiali φ i := by
    funext x; simp [pow_two, Pi.mul_apply]
  rw [this]
  exact (hasCompactSupport_partiali hc i).mul_right

lemma hasCompactSupport_gradNormSq {φ : T3 → ℝ} (hc : HasCompactSupport φ) :
    HasCompactSupport (gradNormSq φ) := by
  have hsum : gradNormSq φ =
      (fun x => partiali φ 0 x ^ 2) + (fun x => partiali φ 1 x ^ 2) +
        (fun x => partiali φ 2 x ^ 2) := by
    funext x
    simp [gradNormSq, Fin.sum_univ_three, Pi.add_apply]
  rw [hsum]
  exact ((hasCompactSupport_sq_partiali hc 0).add
    (hasCompactSupport_sq_partiali hc 1)).add (hasCompactSupport_sq_partiali hc 2)

lemma integrable_cs {f : T3 → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable f volume := by
  have h : Integrable f MeasureTheory.volume :=
    Continuous.integrable_of_hasCompactSupport hf hc
  exact h

/-- Whole-space IBP for compactly supported smooth scalars on ℝ³. -/
theorem integral_partial_mul_cs {f g : T3 → ℝ} (i : Fin 3)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hcf : HasCompactSupport f) (_hcg : HasCompactSupport g) :
    ∫ x, partiali f i x * g x ∂volume =
      -∫ x, f x * partiali g i x ∂volume := by
  have hcont_f : Continuous f := hf.continuous
  have hcont_g : Continuous g := hg.continuous
  have hcont_f' : Continuous (partiali f i) := (contDiff_partiali hf i).continuous
  have hcont_g' : Continuous (partiali g i) := (contDiff_partiali hg i).continuous
  have hf'g : Integrable (fun x => partiali f i x * g x) volume :=
    integrable_cs (hcont_f'.mul hcont_g) (hasCompactSupport_partiali hcf i).mul_right
  have hfg' : Integrable (fun x => f x * partiali g i x) volume :=
    integrable_cs (hcont_f.mul hcont_g') hcf.mul_right
  have hfg : Integrable (fun x => f x * g x) volume :=
    integrable_cs (hcont_f.mul hcont_g) hcf.mul_right
  simpa [partiali] using
    IBPWholeSpace.integral_partial_mul (f := f) (g := g) i hf'g hfg' hfg
      (fun x => hf.differentiable (by simp) x)
      (fun x => hg.differentiable (by simp) x)

lemma partiali_mul {f g : T3 → ℝ} {x : T3} (i : Fin 3)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    partiali (fun y => f y * g y) i x =
      partiali f i x * g x + f x * partiali g i x := by
  simp [partiali, fderiv_fun_mul hf hg]
  ring

lemma partiali_sum {ι : Type*} [Fintype ι] {f : ι → T3 → ℝ} {x : T3} (i : Fin 3)
    (hf : ∀ j, DifferentiableAt ℝ (f j) x) :
    partiali (fun y => ∑ j, f j y) i x = ∑ j, partiali (f j) i x := by
  simp [partiali, fderiv_fun_sum (fun j _ => hf j)]

lemma partiali_sq {f : T3 → ℝ} {x : T3} (i : Fin 3) (hf : DifferentiableAt ℝ f x) :
    partiali (fun y => f y ^ 2) i x = 2 * f x * partiali f i x := by
  have := partiali_mul (f := f) (g := f) (x := x) i hf hf
  simp only [pow_two]
  linarith [this]

lemma partiali_gradNormSq {φ : T3 → ℝ} (hφ : ContDiff ℝ ∞ φ) (i : Fin 3) (x : T3) :
    partiali (gradNormSq φ) i x =
      2 * ∑ j : Fin 3, partiali φ j x * partiali (partiali φ j) i x := by
  have hdiff : ∀ j, DifferentiableAt ℝ (fun y => partiali φ j y ^ 2) x :=
    fun j => ((contDiff_partiali hφ j).pow 2).differentiable (by simp) x
  have hstep := partiali_sum (f := fun j y => partiali φ j y ^ 2) (x := x) i hdiff
  have hsq : ∀ j, partiali (fun y => partiali φ j y ^ 2) i x =
      2 * partiali φ j x * partiali (partiali φ j) i x :=
    fun j => partiali_sq i ((contDiff_partiali hφ j).differentiable (by simp) x)
  have hdef : partiali (gradNormSq φ) i x =
      partiali (fun y => ∑ j : Fin 3, partiali φ j y ^ 2) i x := rfl
  rw [hdef, hstep]
  simp only [hsq, Finset.mul_sum, mul_assoc]

lemma partiali_partiali_mul_gradNormSq {φ : T3 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (i : Fin 3) (x : T3) :
    partiali (fun y => partiali φ i y * gradNormSq φ y) i x =
      partiali (partiali φ i) i x * gradNormSq φ x +
        partiali φ i x * partiali (gradNormSq φ) i x :=
  partiali_mul i
    ((contDiff_partiali hφ i).differentiable (by simp) x)
    ((contDiff_gradNormSq hφ).differentiable (by simp) x)

lemma integrable_partiali_mul_gradNormSq {φ : T3 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (i : Fin 3) :
    Integrable (fun x => partiali φ i x * (partiali φ i x * gradNormSq φ x)) volume :=
  integrable_cs
    ((contDiff_partiali hφ i).continuous.mul
      ((contDiff_partiali hφ i).continuous.mul (contDiff_gradNormSq hφ).continuous))
    (hasCompactSupport_partiali hc i).mul_right

lemma integrable_phi_partiali_g {φ : T3 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (i : Fin 3) :
    Integrable (fun x => φ x *
      partiali (fun y => partiali φ i y * gradNormSq φ y) i x) volume :=
  integrable_cs
    (hφ.continuous.mul
      (contDiff_partiali ((contDiff_partiali hφ i).mul (contDiff_gradNormSq hφ)) i).continuous)
    hc.mul_right

/-- `∫ |∇φ|⁴ = -∫ φ ∑ᵢ ∂ᵢ(∂ᵢ φ · |∇φ|²)` for compactly supported smooth `φ`. -/
theorem integral_gradNormSq_sq {φ : T3 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    ∫ x, gradNormSq φ x ^ 2 ∂volume =
      -∫ x, φ x * ∑ i : Fin 3,
        partiali (fun y => partiali φ i y * gradNormSq φ y) i x ∂volume := by
  have hpoint : ∀ x, gradNormSq φ x ^ 2 =
      ∑ i : Fin 3, partiali φ i x * (partiali φ i x * gradNormSq φ x) := by
    intro x
    rw [pow_two, gradNormSq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hterm : ∀ i,
      ∫ x, partiali φ i x * (partiali φ i x * gradNormSq φ x) ∂volume =
        -∫ x, φ x * partiali (fun y => partiali φ i y * gradNormSq φ y) i x ∂volume := by
    intro i
    have hg : ContDiff ℝ ∞ (fun y => partiali φ i y * gradNormSq φ y) :=
      (contDiff_partiali hφ i).mul (contDiff_gradNormSq hφ)
    have hcg : HasCompactSupport (fun y => partiali φ i y * gradNormSq φ y) :=
      (hasCompactSupport_partiali hc i).mul_right
    simpa [mul_assoc] using integral_partial_mul_cs i hφ hg hc hcg
  have hlhs :
      ∫ x, gradNormSq φ x ^ 2 ∂volume =
        ∑ i : Fin 3, ∫ x, partiali φ i x * (partiali φ i x * gradNormSq φ x) ∂volume := by
    have hfun : (fun x => gradNormSq φ x ^ 2) =
        fun x => ∑ i : Fin 3, partiali φ i x * (partiali φ i x * gradNormSq φ x) :=
      funext hpoint
    rw [hfun, integral_finset_sum]
    intro i _; exact integrable_partiali_mul_gradNormSq hφ hc i
  have hrhs :
      ∑ i : Fin 3, ∫ x, φ x *
          partiali (fun y => partiali φ i y * gradNormSq φ y) i x ∂volume =
        ∫ x, φ x * ∑ i : Fin 3,
          partiali (fun y => partiali φ i y * gradNormSq φ y) i x ∂volume := by
    have hfun : (fun x => φ x * ∑ i : Fin 3,
          partiali (fun y => partiali φ i y * gradNormSq φ y) i x) =
        fun x => ∑ i : Fin 3, φ x *
          partiali (fun y => partiali φ i y * gradNormSq φ y) i x := by
      funext x; simp [Finset.mul_sum]
    rw [hfun]
    exact (integral_finset_sum (Finset.univ : Finset (Fin 3))
      (f := fun (i : Fin 3) (x : T3) => φ x *
        partiali (fun y => partiali φ i y * gradNormSq φ y) i x)
      (fun i _ => integrable_phi_partiali_g hφ hc i)).symm
  rw [hlhs, Finset.sum_congr rfl (fun i _ => hterm i)]
  have hneg :
      ∑ i : Fin 3, -∫ x, φ x *
          partiali (fun y => partiali φ i y * gradNormSq φ y) i x ∂volume =
        -∑ i : Fin 3, ∫ x, φ x *
          partiali (fun y => partiali φ i y * gradNormSq φ y) i x ∂volume :=
    Finset.sum_neg_distrib _
  rw [hneg, hrhs]

/-! ## Compact-support Hölder form of Gagliardo–Nirenberg -/

/-- Hessian energy density `∑_{i,j} (∂ᵢ ∂ⱼ φ)²`. -/
def hessSq (φ : T3 → ℝ) : T3 → ℝ :=
  fun x => ∑ i : Fin 3, ∑ j : Fin 3, partiali (partiali φ i) j x ^ 2

lemma contDiff_hess_component {φ : T3 → ℝ} (hφ : ContDiff ℝ ∞ φ) (i j : Fin 3) :
    ContDiff ℝ ∞ (partiali (partiali φ i) j) :=
  contDiff_partiali (contDiff_partiali hφ i) j

lemma hasCompactSupport_hessSq {φ : T3 → ℝ} (hc : HasCompactSupport φ) :
    HasCompactSupport (hessSq φ) := by
  have hcomp : ∀ i j, HasCompactSupport (fun x => partiali (partiali φ i) j x ^ 2) := by
    intro i j
    have : (fun x => partiali (partiali φ i) j x ^ 2) =
        partiali (partiali φ i) j * partiali (partiali φ i) j := by
      funext x; simp [pow_two, Pi.mul_apply]
    rw [this]
    exact (hasCompactSupport_partiali (hasCompactSupport_partiali hc i) j).mul_right
  have hsum_j : ∀ i, HasCompactSupport (fun x => ∑ j : Fin 3, partiali (partiali φ i) j x ^ 2) := by
    intro i
    have hsum : (fun x => ∑ j : Fin 3, partiali (partiali φ i) j x ^ 2) =
        (fun x => partiali (partiali φ i) 0 x ^ 2) +
          (fun x => partiali (partiali φ i) 1 x ^ 2) +
          (fun x => partiali (partiali φ i) 2 x ^ 2) := by
      funext x; simp [Fin.sum_univ_three, Pi.add_apply]
    rw [hsum]
    exact ((hcomp i 0).add (hcomp i 1)).add (hcomp i 2)
  have hsum : hessSq φ =
      (fun x => ∑ j : Fin 3, partiali (partiali φ 0) j x ^ 2) +
        (fun x => ∑ j : Fin 3, partiali (partiali φ 1) j x ^ 2) +
        (fun x => ∑ j : Fin 3, partiali (partiali φ 2) j x ^ 2) := by
    funext x; simp [hessSq, Fin.sum_univ_three, Pi.add_apply]
  rw [hsum]
  exact ((hsum_j 0).add (hsum_j 1)).add (hsum_j 2)

lemma continuous_hessSq {φ : T3 → ℝ} (hφ : ContDiff ℝ ∞ φ) : Continuous (hessSq φ) :=
  (ContDiff.sum fun i _ =>
    ContDiff.sum fun j _ => (contDiff_hess_component hφ i j).pow 2).continuous

lemma integrable_hessSq {φ : T3 → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Integrable (hessSq φ) volume :=
  integrable_cs (continuous_hessSq hφ) (hasCompactSupport_hessSq hc)

lemma hasCompactSupport_gradNormSq_sq {φ : T3 → ℝ} (hc : HasCompactSupport φ) :
    HasCompactSupport (fun x => gradNormSq φ x ^ 2) := by
  have : (fun x => gradNormSq φ x ^ 2) = gradNormSq φ * gradNormSq φ := by
    funext x; simp [pow_two, Pi.mul_apply]
  rw [this]
  exact (hasCompactSupport_gradNormSq hc).mul_right

lemma integrable_gradNormSq_sq {φ : T3 → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => gradNormSq φ x ^ 2) volume :=
  integrable_cs ((contDiff_gradNormSq hφ).continuous.pow 2)
    (hasCompactSupport_gradNormSq_sq hc)

lemma memLp_cs {f : T3 → ℝ} {p : ENNReal} (hf : Continuous f) (hc : HasCompactSupport f) :
    MemLp f p volume := by
  have h : MemLp f p MeasureTheory.volume :=
    hf.memLp_of_hasCompactSupport (μ := MeasureTheory.volume) hc
  exact h

lemma hasCompactSupport_sqrt_hessSq {φ : T3 → ℝ} (hc : HasCompactSupport φ) :
    HasCompactSupport (fun x => Real.sqrt (hessSq φ x)) :=
  HasCompactSupport.comp_left (g := Real.sqrt) (hasCompactSupport_hessSq hc) Real.sqrt_zero

lemma continuous_sqrt_hessSq {φ : T3 → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    Continuous (fun x => Real.sqrt (hessSq φ x)) :=
  Real.continuous_sqrt.comp (continuous_hessSq hφ)

/-- Cauchy–Schwarz on a finite sum. -/
lemma abs_sum_mul_le_sqrt {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    |∑ i, a i * b i| ≤ Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2) := by
  have hsq : |∑ i, a i * b i| ^ 2 ≤ (∑ i, a i ^ 2) * ∑ i, b i ^ 2 := by
    simpa [abs_sq] using
      Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) a b
  have hsqrt := Real.le_sqrt_of_sq_le hsq
  have hnn : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rwa [Real.sqrt_mul hnn] at hsqrt

lemma abs_sum_diag_le {φ : T3 → ℝ} (x : T3) :
    |∑ i : Fin 3, partiali (partiali φ i) i x| ≤
      Real.sqrt 3 * Real.sqrt (hessSq φ x) := by
  have hcs : (∑ i : Fin 3, |partiali (partiali φ i) i x|) ^ 2 ≤
      3 * ∑ i : Fin 3, partiali (partiali φ i) i x ^ 2 := by
    simpa [sq, abs_sq] using
      (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 3)))
        (f := fun i => |partiali (partiali φ i) i x|))
  have hdiag : ∑ i : Fin 3, partiali (partiali φ i) i x ^ 2 ≤ hessSq φ x := by
    unfold hessSq
    refine Finset.sum_le_sum fun i _ =>
      Finset.single_le_sum (f := fun j : Fin 3 => partiali (partiali φ i) j x ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hsum : |∑ i : Fin 3, partiali (partiali φ i) i x| ≤
      ∑ i : Fin 3, |partiali (partiali φ i) i x| :=
    Finset.abs_sum_le_sum_abs _ _
  have hsqrt : ∑ i : Fin 3, |partiali (partiali φ i) i x| ≤
      Real.sqrt (3 * ∑ i : Fin 3, partiali (partiali φ i) i x ^ 2) :=
    Real.le_sqrt_of_sq_le hcs
  have hsplit : Real.sqrt (3 * ∑ i : Fin 3, partiali (partiali φ i) i x ^ 2) =
      Real.sqrt 3 * Real.sqrt (∑ i : Fin 3, partiali (partiali φ i) i x ^ 2) :=
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 3) _
  have hmon : Real.sqrt (∑ i : Fin 3, partiali (partiali φ i) i x ^ 2) ≤
      Real.sqrt (hessSq φ x) := Real.sqrt_le_sqrt hdiag
  calc
    |∑ i : Fin 3, partiali (partiali φ i) i x|
        ≤ ∑ i : Fin 3, |partiali (partiali φ i) i x| := hsum
    _ ≤ Real.sqrt 3 * Real.sqrt (∑ i : Fin 3, partiali (partiali φ i) i x ^ 2) := by
          rwa [hsplit] at hsqrt
    _ ≤ Real.sqrt 3 * Real.sqrt (hessSq φ x) :=
          mul_le_mul_of_nonneg_left hmon (Real.sqrt_nonneg _)

lemma sum_sq_prod_eq_gradNormSq_sq {φ : T3 → ℝ} (x : T3) :
    ∑ i : Fin 3, ∑ j : Fin 3, (partiali φ i x * partiali φ j x) ^ 2 =
      gradNormSq φ x ^ 2 := by
  have h : ∑ i : Fin 3, ∑ j : Fin 3, partiali φ i x ^ 2 * partiali φ j x ^ 2 =
      (∑ i : Fin 3, partiali φ i x ^ 2) * (∑ j : Fin 3, partiali φ j x ^ 2) := by
    simp_rw [← Finset.mul_sum]
    exact (Finset.sum_mul _ _ _).symm
  calc
    ∑ i : Fin 3, ∑ j : Fin 3, (partiali φ i x * partiali φ j x) ^ 2
        = ∑ i : Fin 3, ∑ j : Fin 3, partiali φ i x ^ 2 * partiali φ j x ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          ring
    _ = gradNormSq φ x ^ 2 := by
          simpa [gradNormSq, pow_two] using h

lemma sum_sum_eq_sum_prod (f : Fin 3 → Fin 3 → ℝ) :
    ∑ i : Fin 3, ∑ j : Fin 3, f i j = ∑ p : Fin 3 × Fin 3, f p.1 p.2 :=
  (Fintype.sum_prod_type (fun p : Fin 3 × Fin 3 => f p.1 p.2)).symm

lemma abs_cross_le {φ : T3 → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : T3) :
    |∑ i : Fin 3, partiali φ i x * partiali (gradNormSq φ) i x| ≤
      2 * Real.sqrt (hessSq φ x) * gradNormSq φ x := by
  have hexp :
      ∑ i : Fin 3, partiali φ i x * partiali (gradNormSq φ) i x =
        2 * ∑ i : Fin 3, ∑ j : Fin 3,
          partiali φ i x * (partiali φ j x * partiali (partiali φ j) i x) := by
    have hx : ∀ i,
        partiali φ i x * partiali (gradNormSq φ) i x =
          2 * ∑ j : Fin 3,
            partiali φ i x * (partiali φ j x * partiali (partiali φ j) i x) := by
      intro i
      rw [partiali_gradNormSq hφ]
      have h2 : partiali φ i x *
          (2 * ∑ j : Fin 3, partiali φ j x * partiali (partiali φ j) i x) =
          2 * (partiali φ i x *
            ∑ j : Fin 3, partiali φ j x * partiali (partiali φ j) i x) := by
        ring
      rw [h2, Finset.mul_sum (s := (Finset.univ : Finset (Fin 3)))
        (a := partiali φ i x)
        (f := fun j => partiali φ j x * partiali (partiali φ j) i x)]
    simp_rw [hx, ← Finset.mul_sum]
  have habs :
      |∑ i : Fin 3, ∑ j : Fin 3,
          partiali φ i x * partiali φ j x * partiali (partiali φ j) i x| ≤
        Real.sqrt (hessSq φ x) * gradNormSq φ x := by
    have hCS :=
      abs_sum_mul_le_sqrt
        (fun p : Fin 3 × Fin 3 => partiali φ p.1 x * partiali φ p.2 x)
        (fun p : Fin 3 × Fin 3 => partiali (partiali φ p.2) p.1 x)
    have hleft :
        ∑ p : Fin 3 × Fin 3,
            (partiali φ p.1 x * partiali φ p.2 x) *
              partiali (partiali φ p.2) p.1 x =
          ∑ i : Fin 3, ∑ j : Fin 3,
            partiali φ i x * partiali φ j x * partiali (partiali φ j) i x := by
      rw [← sum_sum_eq_sum_prod
        (fun i j => partiali φ i x * partiali φ j x * partiali (partiali φ j) i x)]
    have hA : ∑ p : Fin 3 × Fin 3, (partiali φ p.1 x * partiali φ p.2 x) ^ 2 =
        gradNormSq φ x ^ 2 := by
      rw [← sum_sum_eq_sum_prod
        (fun i j => (partiali φ i x * partiali φ j x) ^ 2),
        sum_sq_prod_eq_gradNormSq_sq]
    have hB : ∑ p : Fin 3 × Fin 3, partiali (partiali φ p.2) p.1 x ^ 2 = hessSq φ x := by
      unfold hessSq
      rw [← sum_sum_eq_sum_prod
        (fun i j => partiali (partiali φ j) i x ^ 2), Finset.sum_comm]
    have hnnG : 0 ≤ gradNormSq φ x := Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [hleft] at hCS
    have : Real.sqrt (gradNormSq φ x ^ 2) = gradNormSq φ x :=
      Real.sqrt_sq hnnG
    rw [hA, hB, this, mul_comm] at hCS
    exact hCS
  have h2 : |∑ i : Fin 3, partiali φ i x * partiali (gradNormSq φ) i x| =
      2 * |∑ i : Fin 3, ∑ j : Fin 3,
        partiali φ i x * (partiali φ j x * partiali (partiali φ j) i x)| := by
    rw [hexp, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h2]
  have habs' :
      |∑ i : Fin 3, ∑ j : Fin 3,
          partiali φ i x * (partiali φ j x * partiali (partiali φ j) i x)| ≤
        Real.sqrt (hessSq φ x) * gradNormSq φ x := by
    convert habs using 2
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  nlinarith [Real.sqrt_nonneg (hessSq φ x),
    show 0 ≤ gradNormSq φ x from Finset.sum_nonneg fun _ _ => sq_nonneg _]

lemma abs_ibp_integrand_le {φ : T3 → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : T3) :
    |∑ i : Fin 3, partiali (fun y => partiali φ i y * gradNormSq φ y) i x| ≤
      (Real.sqrt 3 + 2) * Real.sqrt (hessSq φ x) * gradNormSq φ x := by
  have hexp :
      ∑ i : Fin 3, partiali (fun y => partiali φ i y * gradNormSq φ y) i x =
        ∑ i : Fin 3, partiali (partiali φ i) i x * gradNormSq φ x +
          ∑ i : Fin 3, partiali φ i x * partiali (gradNormSq φ) i x := by
    simp_rw [partiali_partiali_mul_gradNormSq hφ]
    exact Finset.sum_add_distrib
  have hnnG : 0 ≤ gradNormSq φ x := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 : |∑ i : Fin 3, partiali (partiali φ i) i x * gradNormSq φ x| ≤
      Real.sqrt 3 * Real.sqrt (hessSq φ x) * gradNormSq φ x := by
    rw [← Finset.sum_mul, abs_mul, abs_of_nonneg hnnG]
    exact mul_le_mul_of_nonneg_right (abs_sum_diag_le (φ := φ) x) hnnG
  have h2 := abs_cross_le hφ x
  have hsplit : |∑ i : Fin 3, partiali (fun y => partiali φ i y * gradNormSq φ y) i x| ≤
      |∑ i : Fin 3, partiali (partiali φ i) i x * gradNormSq φ x| +
        |∑ i : Fin 3, partiali φ i x * partiali (gradNormSq φ) i x| := by
    rw [hexp]; exact abs_add_le _ _
  nlinarith

/-- `∫ |∇φ|⁴ ≤ (√3+2)² M² ∫ |Hess φ|²` for compactly supported smooth `φ` with `|φ| ≤ M`. -/
theorem integral_gradNormSq_sq_le_of_hasCompactSupport {φ : T3 → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) {M : ℝ}
    (hM : ∀ x, |φ x| ≤ M) :
    ∫ x, gradNormSq φ x ^ 2 ∂volume ≤
      (Real.sqrt 3 + 2) ^ 2 * M ^ 2 * ∫ x, hessSq φ x ∂volume := by
  have hM0 : 0 ≤ M := (abs_nonneg (φ 0)).trans (hM 0)
  have hI_eq := integral_gradNormSq_sq hφ hc
  set I := ∫ x, gradNormSq φ x ^ 2 ∂volume
  set H := ∫ x, hessSq φ x ∂volume
  have hInonneg : 0 ≤ I := integral_nonneg fun x => sq_nonneg (gradNormSq φ x)
  have hHnonneg : 0 ≤ H :=
    integral_nonneg fun x =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hinter : Integrable
      (fun x => φ x * ∑ i : Fin 3,
        partiali (fun y => partiali φ i y * gradNormSq φ y) i x) volume := by
    refine integrable_cs ?_ hc.mul_right
    exact hφ.continuous.mul
      (ContDiff.sum fun i _ =>
        contDiff_partiali ((contDiff_partiali hφ i).mul (contDiff_gradNormSq hφ)) i).continuous
  have habsI : |I| ≤ ∫ x, |φ x| *
      |∑ i : Fin 3, partiali (fun y => partiali φ i y * gradNormSq φ y) i x| ∂volume := by
    have hnorm := norm_integral_le_integral_norm (μ := volume)
      (f := fun x => φ x * ∑ i : Fin 3,
        partiali (fun y => partiali φ i y * gradNormSq φ y) i x)
    have hIabs : |I| = |∫ x, φ x * ∑ i : Fin 3,
        partiali (fun y => partiali φ i y * gradNormSq φ y) i x ∂volume| := by
      rw [hI_eq, abs_neg]
    rw [hIabs]
    simpa [abs_mul, Real.norm_eq_abs] using hnorm
  have hpt : ∀ x, |φ x| *
      |∑ i : Fin 3, partiali (fun y => partiali φ i y * gradNormSq φ y) i x| ≤
        (M * (Real.sqrt 3 + 2)) * (Real.sqrt (hessSq φ x) * gradNormSq φ x) := by
    intro x
    have hbound := abs_ibp_integrand_le hφ x
    have hnn : 0 ≤ |∑ i : Fin 3,
        partiali (fun y => partiali φ i y * gradNormSq φ y) i x| := abs_nonneg _
    nlinarith [hM x, hM0, show 0 ≤ Real.sqrt 3 + 2 by positivity,
      Real.sqrt_nonneg (hessSq φ x),
      show 0 ≤ gradNormSq φ x from Finset.sum_nonneg fun _ _ => sq_nonneg _]
  have hint_prod : Integrable
      (fun x => Real.sqrt (hessSq φ x) * gradNormSq φ x) volume :=
    integrable_cs ((continuous_sqrt_hessSq hφ).mul (contDiff_gradNormSq hφ).continuous)
      (hasCompactSupport_sqrt_hessSq hc).mul_right
  have hint_bound : Integrable
      (fun x => (M * (Real.sqrt 3 + 2)) *
        (Real.sqrt (hessSq φ x) * gradNormSq φ x)) volume :=
    hint_prod.const_mul _
  have hmono :
      ∫ x, |φ x| *
          |∑ i : Fin 3, partiali (fun y => partiali φ i y * gradNormSq φ y) i x| ∂volume ≤
        ∫ x, (M * (Real.sqrt 3 + 2)) *
          (Real.sqrt (hessSq φ x) * gradNormSq φ x) ∂volume := by
    refine integral_mono_of_nonneg ?_ hint_bound (Filter.Eventually.of_forall hpt)
    exact Filter.Eventually.of_forall fun _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hCS :
      ∫ x, Real.sqrt (hessSq φ x) * gradNormSq φ x ∂volume ≤
        Real.sqrt H * Real.sqrt I := by
    have hf : MemLp (fun x => Real.sqrt (hessSq φ x)) (ENNReal.ofReal 2) volume :=
      memLp_cs (continuous_sqrt_hessSq hφ) (hasCompactSupport_sqrt_hessSq hc)
    have hg : MemLp (gradNormSq φ) (ENNReal.ofReal 2) volume :=
      memLp_cs (contDiff_gradNormSq hφ).continuous (hasCompactSupport_gradNormSq hc)
    have hnnf : 0 ≤ᵐ[volume] fun x => Real.sqrt (hessSq φ x) :=
      Filter.Eventually.of_forall fun _ => Real.sqrt_nonneg _
    have hnng : 0 ≤ᵐ[volume] gradNormSq φ :=
      Filter.Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume)
      Real.HolderConjugate.two_two hnnf hnng hf hg
    have hnnHess : ∀ x, 0 ≤ hessSq φ x := fun x =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hpowf : ∫ x, Real.sqrt (hessSq φ x) ^ (2 : ℝ) ∂volume = H := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simpa [Real.rpow_two] using Real.sq_sqrt (hnnHess x)
    have hpowg : ∫ x, gradNormSq φ x ^ (2 : ℝ) ∂volume = I := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      exact Real.rpow_natCast _ 2
    calc
      ∫ x, Real.sqrt (hessSq φ x) * gradNormSq φ x ∂volume
          ≤ (∫ x, Real.sqrt (hessSq φ x) ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) *
              (∫ x, gradNormSq φ x ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) := hholder
      _ = H ^ (1 / (2 : ℝ)) * I ^ (1 / (2 : ℝ)) := by rw [hpowf, hpowg]
      _ = Real.sqrt H * Real.sqrt I := by simp [Real.sqrt_eq_rpow]
  have hfactor :
      ∫ x, (M * (Real.sqrt 3 + 2)) *
          (Real.sqrt (hessSq φ x) * gradNormSq φ x) ∂volume =
        (M * (Real.sqrt 3 + 2)) *
          ∫ x, Real.sqrt (hessSq φ x) * gradNormSq φ x ∂volume :=
    integral_const_mul _ _
  have ha0 : 0 ≤ M * (Real.sqrt 3 + 2) :=
    mul_nonneg hM0 (by positivity)
  set a := M * (Real.sqrt 3 + 2) * Real.sqrt H
  have ha : 0 ≤ a := mul_nonneg ha0 (Real.sqrt_nonneg _)
  have hIabs' : I ≤ a * Real.sqrt I := by
    have hAbs : I = |I| := (abs_of_nonneg hInonneg).symm
    have hstep : I ≤ ∫ x, (M * (Real.sqrt 3 + 2)) *
        (Real.sqrt (hessSq φ x) * gradNormSq φ x) ∂volume :=
      (hAbs.trans_le habsI).trans hmono
    have hstep2 : I ≤ (M * (Real.sqrt 3 + 2)) *
        ∫ x, Real.sqrt (hessSq φ x) * gradNormSq φ x ∂volume := by
      rwa [hfactor] at hstep
    have hstep3 : I ≤ (M * (Real.sqrt 3 + 2)) * (Real.sqrt H * Real.sqrt I) :=
      hstep2.trans (mul_le_mul_of_nonneg_left hCS ha0)
    convert hstep3 using 1
    ring
  have hsq : I ^ 2 ≤ a ^ 2 * I := by
    have hR : 0 ≤ a * Real.sqrt I := mul_nonneg ha (Real.sqrt_nonneg _)
    have hpow : I ^ 2 ≤ (a * Real.sqrt I) ^ 2 :=
      sq_le_sq.mpr (by rwa [abs_of_nonneg hInonneg, abs_of_nonneg hR])
    rwa [mul_pow, Real.sq_sqrt hInonneg] at hpow
  have hIle : I ≤ a ^ 2 := by
    by_cases h0 : I = 0
    · simpa [h0] using sq_nonneg a
    · have hpos : 0 < I := lt_of_le_of_ne hInonneg (Ne.symm h0)
      have hmul : I * I ≤ a ^ 2 * I := by simpa [pow_two] using hsq
      exact le_of_mul_le_mul_right hmul hpos
  calc
    I ≤ a ^ 2 := hIle
    _ = (Real.sqrt 3 + 2) ^ 2 * M ^ 2 * H := by
          unfold a
          rw [mul_pow, mul_pow, Real.sq_sqrt hHnonneg]
          ring

/-! ## Cutoff extension of the compact-support Gagliardo–Nirenberg bound -/

open FourierCutoff

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

/-- Second partials of the fixed bump are globally bounded. -/
lemma exists_bound_unitBump_partiali2 :
    ∃ K, 0 ≤ K ∧ ∀ (i j : Fin 3) (y : T3),
      |partiali (partiali (fun z => (unitBump : T3 → ℝ) z) i) j y| ≤ K := by
  let H (i j : Fin 3) : T3 → ℝ :=
    fun y => |partiali (partiali (fun z => (unitBump : T3 → ℝ) z) i) j y|
  let f : T3 → ℝ := fun y => ∑ i : Fin 3, ∑ j : Fin 3, H i j y
  have hcontH : ∀ i j, Continuous (H i j) := fun i j =>
    (contDiff_hess_component contDiff_unitBump i j).continuous.abs
  have hcH : ∀ i j, HasCompactSupport (H i j) := fun i j =>
    HasCompactSupport.comp_left (g := abs)
      (hasCompactSupport_partiali
        (hasCompactSupport_partiali hasCompactSupport_unitBump i) j) abs_zero
  have hf_eq : f =
      (H 0 0 + H 0 1 + H 0 2) + (H 1 0 + H 1 1 + H 1 2) +
        (H 2 0 + H 2 1 + H 2 2) := by
    funext y
    simp [f, H, Fin.sum_univ_three, Pi.add_apply]
  have hcont : Continuous f := by
    rw [hf_eq]
    exact ((((hcontH 0 0).add (hcontH 0 1)).add (hcontH 0 2)).add
      (((hcontH 1 0).add (hcontH 1 1)).add (hcontH 1 2))).add
      (((hcontH 2 0).add (hcontH 2 1)).add (hcontH 2 2))
  have hc : HasCompactSupport f := by
    rw [hf_eq]
    exact ((((hcH 0 0).add (hcH 0 1)).add (hcH 0 2)).add
      (((hcH 1 0).add (hcH 1 1)).add (hcH 1 2))).add
      (((hcH 2 0).add (hcH 2 1)).add (hcH 2 2))
  obtain ⟨K, hK⟩ := hcont.bounded_above_of_compact_support hc
  have hK0 : 0 ≤ K := (norm_nonneg (f 0)).trans (hK 0)
  refine ⟨K, hK0, fun i j y => ?_⟩
  have hnn : 0 ≤ f y :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hfK : f y ≤ K := by
    have := hK y
    simpa [Real.norm_eq_abs, abs_of_nonneg hnn] using this
  have h2 := Finset.single_le_sum
    (f := fun j' : Fin 3 => H i j' y) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have h1 := Finset.single_le_sum
    (f := fun i' : Fin 3 => ∑ j' : Fin 3, H i' j' y)
    (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  exact (h2.trans h1).trans hfK

lemma fderiv_cutoff {R : ℝ} (x : T3) :
    fderiv ℝ (cutoff R) x = R⁻¹ • fderiv ℝ (fun z => (unitBump : T3 → ℝ) z) (R⁻¹ • x) := by
  simpa [cutoff] using
    (fderiv_comp_smul (f := fun z => (unitBump : T3 → ℝ) z) (x := x) R⁻¹)

lemma partiali_cutoff {R : ℝ} (i : Fin 3) (x : T3) :
    partiali (cutoff R) i x =
      R⁻¹ * fderiv ℝ (fun z => (unitBump : T3 → ℝ) z) (R⁻¹ • x) (e i) := by
  simp [partiali, fderiv_cutoff, ContinuousLinearMap.smul_apply, smul_eq_mul]

lemma abs_partiali_cutoff_le {R : ℝ} {K : ℝ}
    (hK : ∀ y, ‖fderiv ℝ (fun z => (unitBump : T3 → ℝ) z) y‖ ≤ K)
    (i : Fin 3) (x : T3) :
    |partiali (cutoff R) i x| ≤ |R⁻¹| * K := by
  rw [partiali_cutoff, abs_mul]
  have h := (hK (R⁻¹ • x)).trans_eq' rfl
  have : |fderiv ℝ (fun z => (unitBump : T3 → ℝ) z) (R⁻¹ • x) (e i)| ≤ K := by
    have hle := (hK (R⁻¹ • x))
    have : |fderiv ℝ (fun z => (unitBump : T3 → ℝ) z) (R⁻¹ • x) (e i)| ≤
        ‖fderiv ℝ (fun z => (unitBump : T3 → ℝ) z) (R⁻¹ • x)‖ * ‖e i‖ :=
      (fderiv ℝ (fun z => (unitBump : T3 → ℝ) z) (R⁻¹ • x)).le_opNorm (e i)
    have he : ‖e i‖ = 1 := by
      simp [e, PiLp.norm_single, Real.norm_eq_abs]
    nlinarith [norm_nonneg (fderiv ℝ (fun z => (unitBump : T3 → ℝ) z) (R⁻¹ • x))]
  exact mul_le_mul_of_nonneg_left this (abs_nonneg _)

/-- Localized function `χ_R φ`. -/
def cutoffMul (R : ℝ) (φ : T3 → ℝ) : T3 → ℝ := fun x => cutoff R x * φ x

lemma contDiff_cutoffMul {R : ℝ} {φ : T3 → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (cutoffMul R φ) :=
  (contDiff_cutoff).mul hφ

lemma hasCompactSupport_cutoffMul {R : ℝ} {φ : T3 → ℝ} (hR : R ≠ 0) :
    HasCompactSupport (cutoffMul R φ) := by
  have : cutoffMul R φ = cutoff R * φ := rfl
  rw [this]
  exact (hasCompactSupport_cutoff hR).mul_right

lemma abs_cutoffMul_le {R : ℝ} {φ : T3 → ℝ} {M : ℝ} (hM : ∀ x, |φ x| ≤ M) (x : T3) :
    |cutoffMul R φ x| ≤ M := by
  have hM0 : 0 ≤ M := (abs_nonneg (φ x)).trans (hM x)
  calc
    |cutoffMul R φ x| = |cutoff R x| * |φ x| := abs_mul _ _
    _ ≤ 1 * |φ x| := mul_le_mul_of_nonneg_right (abs_cutoff_le_one x) (abs_nonneg _)
    _ = |φ x| := one_mul _
    _ ≤ M := hM x

lemma partiali2_cutoff {R : ℝ} (i j : Fin 3) (x : T3) :
    partiali (partiali (cutoff R) i) j x =
      R⁻¹ * R⁻¹ *
        partiali (partiali (fun z => (unitBump : T3 → ℝ) z) i) j (R⁻¹ • x) := by
  have hfun : partiali (cutoff R) i =
      fun y => R⁻¹ * fderiv ℝ (fun z => (unitBump : T3 → ℝ) z) (R⁻¹ • y) (e i) := by
    funext y; exact partiali_cutoff i y
  have hdiff : DifferentiableAt ℝ
      (fun y => fderiv ℝ (fun z => (unitBump : T3 → ℝ) z) (R⁻¹ • y) (e i)) x := by
    have : (fun y => fderiv ℝ (fun z => (unitBump : T3 → ℝ) z) (R⁻¹ • y) (e i)) =
        fun y => partiali (fun z => (unitBump : T3 → ℝ) z) i (R⁻¹ • y) := by
      funext y; rfl
    rw [this]
    exact ((contDiff_partiali contDiff_unitBump i).differentiable (by simp)).comp
      (differentiable_id.const_smul R⁻¹) x
  rw [partiali, hfun]
  have hfun' : (fun y => R⁻¹ * fderiv ℝ (fun z => (unitBump : T3 → ℝ) z) (R⁻¹ • y) (e i)) =
      fun y => R⁻¹ • fderiv ℝ (fun z => (unitBump : T3 → ℝ) z) (R⁻¹ • y) (e i) := by
    funext y; rw [smul_eq_mul]
  rw [hfun', fderiv_fun_const_smul hdiff R⁻¹, ContinuousLinearMap.smul_apply]
  rw [fderiv_comp_smul
    (f := fun z => fderiv ℝ (fun w => (unitBump : T3 → ℝ) w) z (e i)) (x := x) R⁻¹]
  have hpart : (fun z => fderiv ℝ (fun w => (unitBump : T3 → ℝ) w) z (e i)) =
      partiali (fun w => (unitBump : T3 → ℝ) w) i := rfl
  simp [hpart, partiali, ContinuousLinearMap.smul_apply, smul_eq_mul, mul_assoc]

lemma abs_partiali2_cutoff_le {R : ℝ} {K : ℝ}
    (hK : ∀ (i j : Fin 3) (y : T3),
      |partiali (partiali (fun z => (unitBump : T3 → ℝ) z) i) j y| ≤ K)
    (i j : Fin 3) (x : T3) :
    |partiali (partiali (cutoff R) i) j x| ≤ |R⁻¹| * |R⁻¹| * K := by
  rw [partiali2_cutoff, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hK i j (R⁻¹ • x))
    (mul_nonneg (abs_nonneg _) (abs_nonneg _))

lemma partiali_cutoffMul {R : ℝ} {φ : T3 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (i : Fin 3) (x : T3) :
    partiali (cutoffMul R φ) i x =
      partiali (cutoff R) i x * φ x + cutoff R x * partiali φ i x :=
  partiali_mul i (contDiff_cutoff.differentiable (by simp) x)
    (hφ.differentiable (by simp) x)

lemma partiali_add {f g : T3 → ℝ} {x : T3} (i : Fin 3)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    partiali (fun y => f y + g y) i x = partiali f i x + partiali g i x := by
  simp [partiali, fderiv_fun_add hf hg]

lemma partiali2_cutoffMul {R : ℝ} {φ : T3 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (i j : Fin 3) (x : T3) :
    partiali (partiali (cutoffMul R φ) i) j x =
      partiali (partiali (cutoff R) i) j x * φ x +
        partiali (cutoff R) i x * partiali φ j x +
        partiali (cutoff R) j x * partiali φ i x +
        cutoff R x * partiali (partiali φ i) j x := by
  have hfun : partiali (cutoffMul R φ) i =
      fun y => partiali (cutoff R) i y * φ y + cutoff R y * partiali φ i y := by
    funext y; exact partiali_cutoffMul hφ i y
  have hχ : DifferentiableAt ℝ (partiali (cutoff R) i) x :=
    (contDiff_partiali (contDiff_cutoff (R := R)) i).differentiable (by simp) x
  have hφd : DifferentiableAt ℝ φ x := hφ.differentiable (by simp) x
  have hχ0 : DifferentiableAt ℝ (cutoff R) x :=
    contDiff_cutoff.differentiable (by simp) x
  have hφi : DifferentiableAt ℝ (partiali φ i) x :=
    (contDiff_partiali hφ i).differentiable (by simp) x
  rw [hfun]
  rw [partiali_add (f := fun y => partiali (cutoff R) i y * φ y)
    (g := fun y => cutoff R y * partiali φ i y) (x := x) j
    (hχ.mul hφd) (hχ0.mul hφi)]
  have hleft :=
    partiali_mul (f := partiali (cutoff R) i) (g := φ) (x := x) j hχ hφd
  have hright :=
    partiali_mul (f := cutoff R) (g := partiali φ i) (x := x) j hχ0 hφi
  rw [hleft, hright]
  ring

/-- `(a+b+c+d)² ≤ 4(a²+b²+c²+d²)`. -/
lemma four_mul_sq_le (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  have := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (Fin 4)))
    (f := (![a, b, c, d] : Fin 4 → ℝ))
  simpa [Fin.sum_univ_four] using this

/-- Direct whole-space IBP on `φ` itself is not available from finite H²
energy alone: the integrand `|∇φ|⁴` is the quantity being bounded, so the
integrability hypotheses of `IBPWholeSpace` are not known a priori. The
cutoff `χ_R φ` restores compact support (hence integrability), and the
`R → ∞` limit is taken by Fatou. -/
lemma abs_partiali2_cutoffMul_le {R : ℝ} {φ : T3 → ℝ} {K1 K2 : ℝ}
    (hφ : ContDiff ℝ ∞ φ)
    (hK1 : ∀ (i : Fin 3) (x : T3), |partiali (cutoff R) i x| ≤ |R⁻¹| * K1)
    (hK2 : ∀ (i j : Fin 3) (x : T3),
      |partiali (partiali (cutoff R) i) j x| ≤ |R⁻¹| * |R⁻¹| * K2)
    (hK2nn : 0 ≤ K2) (i j : Fin 3) (x : T3) :
    |partiali (partiali (cutoffMul R φ) i) j x| ≤
      |R⁻¹| * |R⁻¹| * K2 * |φ x| + |R⁻¹| * K1 * |partiali φ j x| +
        |R⁻¹| * K1 * |partiali φ i x| + |partiali (partiali φ i) j x| := by
  have hexp := partiali2_cutoffMul (R := R) hφ i j x
  have ha : |partiali (partiali (cutoff R) i) j x * φ x| ≤
      |R⁻¹| * |R⁻¹| * K2 * |φ x| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hK2 i j x) (abs_nonneg _)
  have hb : |partiali (cutoff R) i x * partiali φ j x| ≤
      |R⁻¹| * K1 * |partiali φ j x| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hK1 i x) (abs_nonneg _)
  have hc : |partiali (cutoff R) j x * partiali φ i x| ≤
      |R⁻¹| * K1 * |partiali φ i x| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hK1 j x) (abs_nonneg _)
  have hd : |cutoff R x * partiali (partiali φ i) j x| ≤
      |partiali (partiali φ i) j x| := by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (abs_cutoff_le_one x)
  have hsplit :
      |partiali (partiali (cutoff R) i) j x * φ x +
          partiali (cutoff R) i x * partiali φ j x +
          partiali (cutoff R) j x * partiali φ i x +
          cutoff R x * partiali (partiali φ i) j x| ≤
        |partiali (partiali (cutoff R) i) j x * φ x| +
          |partiali (cutoff R) i x * partiali φ j x| +
          |partiali (cutoff R) j x * partiali φ i x| +
          |cutoff R x * partiali (partiali φ i) j x| := by
    set a := partiali (partiali (cutoff R) i) j x * φ x
    set b := partiali (cutoff R) i x * partiali φ j x
    set c := partiali (cutoff R) j x * partiali φ i x
    set d := cutoff R x * partiali (partiali φ i) j x
    calc
      |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
      _ ≤ |a + b| + |c| + |d| := by
            gcongr; exact abs_add_le _ _
      _ ≤ |a| + |b| + |c| + |d| := by
            gcongr; exact abs_add_le _ _
  rw [hexp]
  nlinarith [hsplit, ha, hb, hc, hd]

lemma iteratedFDeriv_two_eq_partiali {φ : T3 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (i j : Fin 3) (x : T3) :
    iteratedFDeriv ℝ 2 φ x (U (![i, j])) = partiali (partiali φ j) i x := by
  have hDu : DifferentiableAt ℝ (fderiv ℝ (φ : T3 → ℝ)) x :=
    (hφ.fderiv_right (m := ∞) le_rfl).differentiable (by simp) x
  have hcomp :
      fderiv ℝ (fun y => fderiv ℝ (φ : T3 → ℝ) y (e j)) x (e i) =
        (fderiv ℝ (fderiv ℝ (φ : T3 → ℝ)) x (e i)) (e j) := by
    have hfun : (fun y => fderiv ℝ (φ : T3 → ℝ) y (e j)) =
        ⇑(ContinuousLinearMap.apply ℝ ℝ (e j)) ∘ fderiv ℝ (φ : T3 → ℝ) := rfl
    rw [hfun, fderiv_comp (f := fderiv ℝ (φ : T3 → ℝ))
      (g := ⇑(ContinuousLinearMap.apply ℝ ℝ (e j))) (x := x)
      (ContinuousLinearMap.apply ℝ ℝ (e j)).differentiableAt hDu,
      ContinuousLinearMap.fderiv]
    rfl
  rw [iteratedFDeriv_two_apply, partiali]
  have hU0 : (U (![i, j]) : Fin 2 → T3) 0 = e i := by simp [U, e]
  have hU1 : (U (![i, j]) : Fin 2 → T3) 1 = e j := by simp [U, e]
  rw [hU0, hU1, hcomp.symm]
  rfl

lemma hessSq_eq_sum_iter {φ : T3 → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : T3) :
    hessSq φ x = ∑ α : Fin 2 → Fin 3, iteratedFDeriv ℝ 2 φ x (U α) ^ 2 := by
  have hsum :
      ∑ α : Fin 2 → Fin 3, iteratedFDeriv ℝ 2 φ x (U α) ^ 2 =
        ∑ i : Fin 3, ∑ j : Fin 3, iteratedFDeriv ℝ 2 φ x (U (![i, j])) ^ 2 := by
    have h := Fintype.sum_equiv (piFinTwoEquiv fun _ : Fin 2 => Fin 3)
      (fun α => iteratedFDeriv ℝ 2 φ x (U α) ^ 2)
      (fun p : Fin 3 × Fin 3 => iteratedFDeriv ℝ 2 φ x (U (![p.1, p.2])) ^ 2)
    refine (h ?_).trans ?_
    · intro α
      have hα : (![α 0, α 1] : Fin 2 → Fin 3) = α := by
        ext k; fin_cases k <;> simp
      have hp : (piFinTwoEquiv fun _ : Fin 2 => Fin 3) α = (α 0, α 1) := rfl
      simp [hp, hα]
    · exact (sum_sum_eq_sum_prod
        (fun i j => iteratedFDeriv ℝ 2 φ x (U (![i, j])) ^ 2)).symm
  unfold hessSq
  have hterm : ∑ i : Fin 3, ∑ j : Fin 3, partiali (partiali φ i) j x ^ 2 =
      ∑ i : Fin 3, ∑ j : Fin 3, iteratedFDeriv ℝ 2 φ x (U (![j, i])) ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    exact congrArg (fun z : ℝ => z ^ 2) (iteratedFDeriv_two_eq_partiali hφ j i x).symm
  rw [hterm, Finset.sum_comm]
  exact hsum.symm

lemma gradNormSq_eq_sum_iter (φ : T3 → ℝ) (x : T3) :
    gradNormSq φ x = ∑ α : Fin 1 → Fin 3, iteratedFDeriv ℝ 1 φ x (U α) ^ 2 := by
  have hsum : ∑ α : Fin 1 → Fin 3, iteratedFDeriv ℝ 1 φ x (U α) ^ 2 =
      ∑ i : Fin 3, iteratedFDeriv ℝ 1 φ x (U (fun _ => i)) ^ 2 := by
    refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 3))
      (fun α => iteratedFDeriv ℝ 1 φ x (U α) ^ 2)
      (fun i => iteratedFDeriv ℝ 1 φ x (U (fun _ => i)) ^ 2) ?_
    intro α
    have hα : (fun _ : Fin 1 => Equiv.funUnique (Fin 1) (Fin 3) α) = α := by
      ext k
      have : k = 0 := Subsingleton.elim k 0
      simp [this, Equiv.funUnique]
    simp [hα]
  rw [hsum]
  unfold gradNormSq
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_one_apply]
  simp [partiali, U, e]

lemma ofReal_sq_iter {k : ℕ} (φ : T3 → ℝ) (α : Fin k → Fin 3) (x : T3) :
    ENNReal.ofReal (iteratedFDeriv ℝ k φ x (U α) ^ 2) =
      ‖iteratedFDeriv ℝ k φ x (U α)‖ₑ ^ 2 := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

lemma continuous_iter_apply {k : ℕ} {φ : T3 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (α : Fin k → Fin 3) :
    Continuous (fun x => iteratedFDeriv ℝ k φ x (U α)) :=
  (continuous_eval_const (U α)).comp
    (hφ.continuous_iteratedFDeriv (m := k) (by exact_mod_cast le_top))

lemma aemeasurable_iter_sq {k : ℕ} {φ : T3 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (α : Fin k → Fin 3) :
    AEMeasurable (fun x => ‖iteratedFDeriv ℝ k φ x (U α)‖ₑ ^ 2) volume :=
  (continuous_iter_apply hφ α).aestronglyMeasurable.enorm.pow_const 2

lemma lintegral_hessSq_le_energyR {φ : T3 → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ∫⁻ x, ENNReal.ofReal (hessSq φ x) ∂volume ≤ energyR 2 φ := by
  have hpt : (fun x => ENNReal.ofReal (hessSq φ x)) =
      fun x => ∑ α : Fin 2 → Fin 3, ‖iteratedFDeriv ℝ 2 φ x (U α)‖ₑ ^ 2 := by
    funext x
    rw [hessSq_eq_sum_iter hφ x, ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    refine Finset.sum_congr rfl fun α _ => ofReal_sq_iter (k := 2) φ α x
  rw [hpt, lintegral_finset_sum' (Finset.univ : Finset (Fin 2 → Fin 3))
    (fun α _ => aemeasurable_iter_sq (k := 2) hφ α)]
  unfold energyR
  have hmem : (2 : ℕ) ∈ Finset.range 3 := by simp
  exact Finset.single_le_sum
    (f := fun k : ℕ => ∑ α : Fin k → Fin 3,
      ∫⁻ x, ‖iteratedFDeriv ℝ k φ x (U α)‖ₑ ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => zero_le _) hmem

lemma lintegral_gradNormSq_le_energyR (φ : T3 → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    ∫⁻ x, ENNReal.ofReal (gradNormSq φ x) ∂volume ≤ energyR 2 φ := by
  have hpt : (fun x => ENNReal.ofReal (gradNormSq φ x)) =
      fun x => ∑ α : Fin 1 → Fin 3, ‖iteratedFDeriv ℝ 1 φ x (U α)‖ₑ ^ 2 := by
    funext x
    rw [gradNormSq_eq_sum_iter φ x,
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    refine Finset.sum_congr rfl fun α _ => ofReal_sq_iter (k := 1) φ α x
  rw [hpt, lintegral_finset_sum' (Finset.univ : Finset (Fin 1 → Fin 3))
    (fun α _ => aemeasurable_iter_sq (k := 1) hφ α)]
  unfold energyR
  have hmem : (1 : ℕ) ∈ Finset.range 3 := by simp
  exact Finset.single_le_sum
    (f := fun k : ℕ => ∑ α : Fin k → Fin 3,
      ∫⁻ x, ‖iteratedFDeriv ℝ k φ x (U α)‖ₑ ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => zero_le _) hmem

lemma lintegral_sq_le_energyR (φ : T3 → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    ∫⁻ x, ENNReal.ofReal (φ x ^ 2) ∂volume ≤ energyR 2 φ := by
  have hpt : (fun x => ENNReal.ofReal (φ x ^ 2)) =
      fun x => ∑ α : Fin 0 → Fin 3, ‖iteratedFDeriv ℝ 0 φ x (U α)‖ₑ ^ 2 := by
    funext x
    have hsum : ∑ α : Fin 0 → Fin 3, ‖iteratedFDeriv ℝ 0 φ x (U α)‖ₑ ^ 2 =
        ‖φ x‖ₑ ^ 2 := by
      simp [iteratedFDeriv_zero_apply, Finset.univ_unique]
    rw [hsum, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [hpt, lintegral_finset_sum' (Finset.univ : Finset (Fin 0 → Fin 3))
    (fun α _ => aemeasurable_iter_sq (k := 0) hφ α)]
  unfold energyR
  have hmem : (0 : ℕ) ∈ Finset.range 3 := by simp
  exact Finset.single_le_sum
    (f := fun k : ℕ => ∑ α : Fin k → Fin 3,
      ∫⁻ x, ‖iteratedFDeriv ℝ k φ x (U α)‖ₑ ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => zero_le _) hmem

lemma integrable_of_lintegral_ofReal {f : T3 → ℝ} (hcont : Continuous f)
    (hnn : ∀ x, 0 ≤ f x) (hfin : ∫⁻ x, ENNReal.ofReal (f x) ∂volume < ⊤) :
    Integrable f volume := by
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  change ∫⁻ x, ‖f x‖ₑ ∂volume < ⊤
  have : ∫⁻ x, ‖f x‖ₑ ∂volume = ∫⁻ x, ENNReal.ofReal (f x) ∂volume :=
    lintegral_congr fun x => by
      simp [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hnn x)]
  rwa [this]

lemma integrable_hessSq_of_energy {φ : T3 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hE : energyR 2 φ < ⊤) : Integrable (hessSq φ) volume :=
  integrable_of_lintegral_ofReal (continuous_hessSq hφ)
    (fun _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    ((lintegral_hessSq_le_energyR hφ).trans_lt hE)

lemma integrable_gradNormSq_of_energy {φ : T3 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hE : energyR 2 φ < ⊤) : Integrable (gradNormSq φ) volume :=
  integrable_of_lintegral_ofReal (contDiff_gradNormSq hφ).continuous
    (fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    ((lintegral_gradNormSq_le_energyR φ hφ).trans_lt hE)

lemma integrable_sq_of_energy {φ : T3 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hE : energyR 2 φ < ⊤) : Integrable (fun x => φ x ^ 2) volume :=
  integrable_of_lintegral_ofReal (hφ.continuous.pow 2)
    (fun _ => sq_nonneg _)
    ((lintegral_sq_le_energyR φ hφ).trans_lt hE)

lemma integral_le_toReal_of_lintegral {f : T3 → ℝ}
    (hint : Integrable f volume) (hnn : ∀ x, 0 ≤ f x)
    {b : ENNReal} (hle : ∫⁻ x, ENNReal.ofReal (f x) ∂volume ≤ b)
    (hb : b ≠ ⊤) :
    ∫ x, f x ∂volume ≤ b.toReal := by
  have : ENNReal.ofReal (∫ x, f x ∂volume) =
      ∫⁻ x, ENNReal.ofReal (f x) ∂volume :=
    ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn)
  have hbound : ENNReal.ofReal (∫ x, f x ∂volume) ≤ b := this.trans_le hle
  exact (ENNReal.ofReal_le_iff_le_toReal hb).mp hbound

lemma integral_hessSq_le_energyR {φ : T3 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hE : energyR 2 φ < ⊤) :
    ∫ x, hessSq φ x ∂volume ≤ (energyR 2 φ).toReal :=
  integral_le_toReal_of_lintegral (integrable_hessSq_of_energy hφ hE)
    (fun _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (lintegral_hessSq_le_energyR hφ) hE.ne

lemma integral_gradNormSq_le_energyR {φ : T3 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hE : energyR 2 φ < ⊤) :
    ∫ x, gradNormSq φ x ∂volume ≤ (energyR 2 φ).toReal :=
  integral_le_toReal_of_lintegral (integrable_gradNormSq_of_energy hφ hE)
    (fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (lintegral_gradNormSq_le_energyR φ hφ) hE.ne

lemma integral_sq_le_energyR {φ : T3 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hE : energyR 2 φ < ⊤) :
    ∫ x, φ x ^ 2 ∂volume ≤ (energyR 2 φ).toReal :=
  integral_le_toReal_of_lintegral (integrable_sq_of_energy hφ hE)
    (fun _ => sq_nonneg _) (lintegral_sq_le_energyR φ hφ) hE.ne

lemma abs_inv_le_one_of_one_le {R : ℝ} (hR : 1 ≤ R) : |R⁻¹| ≤ 1 := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  rw [abs_inv, abs_of_nonneg hR0]
  exact inv_le_one_of_one_le₀ hR

lemma cutoffMul_eq_of_mem_closedBall {R : ℝ} (hR : 0 < R) {φ : T3 → ℝ} {x : T3}
    (hx : x ∈ Metric.closedBall (0 : T3) R) :
    cutoffMul R φ x = φ x := by
  simp [cutoffMul, cutoff_eq_one_of_le hR (by simpa [dist_zero_right] using hx)]

lemma cutoffMul_eventuallyEq {R : ℝ} (hR : 0 < R) (φ : T3 → ℝ) {x : T3}
    (hx : ‖x‖ < R) : cutoffMul R φ =ᶠ[nhds x] φ := by
  have hx' : x ∈ Metric.ball (0 : T3) R := by
    simpa [Metric.mem_ball, dist_zero_right] using hx
  exact Filter.eventuallyEq_of_mem (IsOpen.mem_nhds Metric.isOpen_ball hx')
    fun y hy => cutoffMul_eq_of_mem_closedBall hR (Metric.ball_subset_closedBall hy)

lemma partiali_cutoffMul_eq_of_lt {R : ℝ} (hR : 0 < R) {φ : T3 → ℝ}
    (i : Fin 3) {x : T3} (hx : ‖x‖ < R) :
    partiali (cutoffMul R φ) i x = partiali φ i x := by
  simp [partiali, Filter.EventuallyEq.fderiv_eq (cutoffMul_eventuallyEq hR φ hx)]

lemma gradNormSq_cutoffMul_eq_of_lt {R : ℝ} (hR : 0 < R) {φ : T3 → ℝ}
    {x : T3} (hx : ‖x‖ < R) :
    gradNormSq (cutoffMul R φ) x = gradNormSq φ x := by
  unfold gradNormSq
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [partiali_cutoffMul_eq_of_lt hR i hx]

lemma hessSq_cutoffMul_le {R : ℝ} (hR : 1 ≤ R) {φ : T3 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {K1 K2 : ℝ} (hK1nn : 0 ≤ K1) (hK2nn : 0 ≤ K2)
    (hK1 : ∀ (i : Fin 3) (x : T3), |partiali (cutoff R) i x| ≤ |R⁻¹| * K1)
    (hK2 : ∀ (i j : Fin 3) (x : T3),
      |partiali (partiali (cutoff R) i) j x| ≤ |R⁻¹| * |R⁻¹| * K2)
    (x : T3) :
    hessSq (cutoffMul R φ) x ≤
      (36 * K2 ^ 2 + 24 * K1 ^ 2 + 4) *
        (φ x ^ 2 + gradNormSq φ x + hessSq φ x) := by
  have hinv := abs_inv_le_one_of_one_le hR
  have hpt : ∀ (i j : Fin 3),
      |partiali (partiali (cutoffMul R φ) i) j x| ≤
        K2 * |φ x| + K1 * |partiali φ j x| + K1 * |partiali φ i x| +
          |partiali (partiali φ i) j x| := by
    intro i j
    have h := abs_partiali2_cutoffMul_le (R := R) hφ hK1 hK2 hK2nn i j x
    have ha : |R⁻¹| * |R⁻¹| * K2 * |φ x| ≤ K2 * |φ x| := by
      have hinv2 : |R⁻¹| * |R⁻¹| ≤ 1 := mul_le_one₀ hinv (abs_nonneg _) hinv
      calc
        |R⁻¹| * |R⁻¹| * K2 * |φ x| = (|R⁻¹| * |R⁻¹|) * (K2 * |φ x|) := by ring
        _ ≤ 1 * (K2 * |φ x|) :=
          mul_le_mul_of_nonneg_right hinv2 (mul_nonneg hK2nn (abs_nonneg _))
        _ = K2 * |φ x| := one_mul _
    have hb : |R⁻¹| * K1 * |partiali φ j x| ≤ K1 * |partiali φ j x| :=
      mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hK1nn hinv) (abs_nonneg _)
    have hc : |R⁻¹| * K1 * |partiali φ i x| ≤ K1 * |partiali φ i x| :=
      mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hK1nn hinv) (abs_nonneg _)
    nlinarith
  have hsq : ∀ (i j : Fin 3),
      partiali (partiali (cutoffMul R φ) i) j x ^ 2 ≤
        4 * (K2 ^ 2 * φ x ^ 2 + K1 ^ 2 * partiali φ j x ^ 2 +
          K1 ^ 2 * partiali φ i x ^ 2 + partiali (partiali φ i) j x ^ 2) := by
    intro i j
    have hpow : |partiali (partiali (cutoffMul R φ) i) j x| ^ 2 ≤
        (K2 * |φ x| + K1 * |partiali φ j x| + K1 * |partiali φ i x| +
          |partiali (partiali φ i) j x|) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) (hpt i j) 2
    have hfour := four_mul_sq_le (K2 * |φ x|) (K1 * |partiali φ j x|)
      (K1 * |partiali φ i x|) (|partiali (partiali φ i) j x|)
    have hpow' : partiali (partiali (cutoffMul R φ) i) j x ^ 2 ≤
        (K2 * |φ x| + K1 * |partiali φ j x| + K1 * |partiali φ i x| +
          |partiali (partiali φ i) j x|) ^ 2 := by
      simpa [sq_abs] using hpow
    have hcomb := hpow'.trans hfour
    have hrw :
        4 * ((K2 * |φ x|) ^ 2 + (K1 * |partiali φ j x|) ^ 2 +
          (K1 * |partiali φ i x|) ^ 2 + |partiali (partiali φ i) j x| ^ 2) =
        4 * (K2 ^ 2 * φ x ^ 2 + K1 ^ 2 * partiali φ j x ^ 2 +
          K1 ^ 2 * partiali φ i x ^ 2 + partiali (partiali φ i) j x ^ 2) := by
      simp [mul_pow, sq_abs]
    exact hcomb.trans_eq hrw
  have hsum :
      hessSq (cutoffMul R φ) x ≤
        4 * ∑ i : Fin 3, ∑ j : Fin 3,
          (K2 ^ 2 * φ x ^ 2 + K1 ^ 2 * partiali φ j x ^ 2 +
            K1 ^ 2 * partiali φ i x ^ 2 + partiali (partiali φ i) j x ^ 2) := by
    unfold hessSq
    calc
      ∑ i : Fin 3, ∑ j : Fin 3,
          partiali (partiali (cutoffMul R φ) i) j x ^ 2
          ≤ ∑ i : Fin 3, ∑ j : Fin 3,
              4 * (K2 ^ 2 * φ x ^ 2 + K1 ^ 2 * partiali φ j x ^ 2 +
                K1 ^ 2 * partiali φ i x ^ 2 +
                  partiali (partiali φ i) j x ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hsq i j
      _ = 4 * ∑ i : Fin 3, ∑ j : Fin 3,
            (K2 ^ 2 * φ x ^ 2 + K1 ^ 2 * partiali φ j x ^ 2 +
              K1 ^ 2 * partiali φ i x ^ 2 +
                partiali (partiali φ i) j x ^ 2) := by
        simp [Finset.mul_sum]
  have h9 : ∑ i : Fin 3, ∑ j : Fin 3, K2 ^ 2 * φ x ^ 2 = 9 * K2 ^ 2 * φ x ^ 2 := by
    simp [Finset.sum_const, Fintype.card_fin]; ring
  have hj : ∑ i : Fin 3, ∑ j : Fin 3, K1 ^ 2 * partiali φ j x ^ 2 =
      3 * K1 ^ 2 * gradNormSq φ x := by
    calc
      ∑ i : Fin 3, ∑ j : Fin 3, K1 ^ 2 * partiali φ j x ^ 2 =
          ∑ i : Fin 3, K1 ^ 2 * ∑ j : Fin 3, partiali φ j x ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ i : Fin 3, K1 ^ 2 * gradNormSq φ x := by
        simp [gradNormSq]
      _ = 3 * (K1 ^ 2 * gradNormSq φ x) := by
        simp [Finset.sum_const, Fintype.card_fin]
      _ = 3 * K1 ^ 2 * gradNormSq φ x := by ring
  have hi : ∑ i : Fin 3, ∑ j : Fin 3, K1 ^ 2 * partiali φ i x ^ 2 =
      3 * K1 ^ 2 * gradNormSq φ x := by
    calc
      ∑ i : Fin 3, ∑ j : Fin 3, K1 ^ 2 * partiali φ i x ^ 2 =
          ∑ i : Fin 3, ∑ j : Fin 3, K1 ^ 2 * partiali φ i x ^ 2 := rfl
      _ = ∑ i : Fin 3, 3 * (K1 ^ 2 * partiali φ i x ^ 2) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [Finset.sum_const, Fintype.card_fin]
      _ = 3 * ∑ i : Fin 3, K1 ^ 2 * partiali φ i x ^ 2 := by
        rw [Finset.mul_sum]
      _ = 3 * (K1 ^ 2 * ∑ i : Fin 3, partiali φ i x ^ 2) := by
        simp only [← Finset.mul_sum]
      _ = 3 * K1 ^ 2 * gradNormSq φ x := by
        simp [gradNormSq]; ring
  have hexpand :
      ∑ i : Fin 3, ∑ j : Fin 3,
          (K2 ^ 2 * φ x ^ 2 + K1 ^ 2 * partiali φ j x ^ 2 +
            K1 ^ 2 * partiali φ i x ^ 2 + partiali (partiali φ i) j x ^ 2) =
        9 * K2 ^ 2 * φ x ^ 2 + 6 * K1 ^ 2 * gradNormSq φ x + hessSq φ x := by
    simp_rw [Finset.sum_add_distrib]
    rw [h9, hj, hi]
    simp [hessSq]; ring
  have hC : 0 ≤ 36 * K2 ^ 2 + 24 * K1 ^ 2 + 4 := by
    nlinarith [sq_nonneg K1, sq_nonneg K2]
  have hφ2 : 0 ≤ φ x ^ 2 := sq_nonneg _
  have hg : 0 ≤ gradNormSq φ x := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hH : 0 ≤ hessSq φ x :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have : 4 * (9 * K2 ^ 2 * φ x ^ 2 + 6 * K1 ^ 2 * gradNormSq φ x + hessSq φ x) ≤
      (36 * K2 ^ 2 + 24 * K1 ^ 2 + 4) * (φ x ^ 2 + gradNormSq φ x + hessSq φ x) := by
    nlinarith [sq_nonneg K1, sq_nonneg K2]
  calc
    hessSq (cutoffMul R φ) x
        ≤ 4 * ∑ i : Fin 3, ∑ j : Fin 3,
            (K2 ^ 2 * φ x ^ 2 + K1 ^ 2 * partiali φ j x ^ 2 +
              K1 ^ 2 * partiali φ i x ^ 2 +
                partiali (partiali φ i) j x ^ 2) := hsum
    _ = 4 * (9 * K2 ^ 2 * φ x ^ 2 + 6 * K1 ^ 2 * gradNormSq φ x + hessSq φ x) := by
        rw [hexpand]
    _ ≤ _ := this

lemma integral_three_energy {φ : T3 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hE : energyR 2 φ < ⊤) :
    ∫ x, φ x ^ 2 ∂volume + ∫ x, gradNormSq φ x ∂volume + ∫ x, hessSq φ x ∂volume ≤
      3 * (energyR 2 φ).toReal := by
  nlinarith [integral_sq_le_energyR hφ hE, integral_gradNormSq_le_energyR hφ hE,
    integral_hessSq_le_energyR hφ hE]

lemma integral_hessSq_cutoffMul_le {R : ℝ} (hR : 1 ≤ R) {φ : T3 → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hE : energyR 2 φ < ⊤) {K1 K2 : ℝ}
    (hK1nn : 0 ≤ K1) (hK2nn : 0 ≤ K2)
    (hK1 : ∀ (i : Fin 3) (x : T3), |partiali (cutoff R) i x| ≤ |R⁻¹| * K1)
    (hK2 : ∀ (i j : Fin 3) (x : T3),
      |partiali (partiali (cutoff R) i) j x| ≤ |R⁻¹| * |R⁻¹| * K2) :
    ∫ x, hessSq (cutoffMul R φ) x ∂volume ≤
      (36 * K2 ^ 2 + 24 * K1 ^ 2 + 4) * 3 * (energyR 2 φ).toReal := by
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  let C0 : ℝ := 36 * K2 ^ 2 + 24 * K1 ^ 2 + 4
  have hpt := hessSq_cutoffMul_le hR hφ hK1nn hK2nn hK1 hK2
  have hnn : ∀ x, 0 ≤ hessSq (cutoffMul R φ) x := fun x =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hinter : Integrable
      (fun x => C0 * (φ x ^ 2 + gradNormSq φ x + hessSq φ x)) volume := by
    exact (((integrable_sq_of_energy hφ hE).add
      (integrable_gradNormSq_of_energy hφ hE)).add
      (integrable_hessSq_of_energy hφ hE)).const_mul C0
  have hmono := integral_mono_of_nonneg (Filter.Eventually.of_forall hnn) hinter
    (Filter.Eventually.of_forall hpt)
  have hrhs :
      ∫ x, C0 * (φ x ^ 2 + gradNormSq φ x + hessSq φ x) ∂volume =
        C0 * (∫ x, φ x ^ 2 ∂volume + ∫ x, gradNormSq φ x ∂volume +
            ∫ x, hessSq φ x ∂volume) := by
    have hφg : Integrable (fun a => φ a ^ 2 + gradNormSq φ a) volume :=
      (integrable_sq_of_energy hφ hE).add (integrable_gradNormSq_of_energy hφ hE)
    rw [integral_const_mul,
      integral_add hφg (integrable_hessSq_of_energy hφ hE),
      integral_add (integrable_sq_of_energy hφ hE)
        (integrable_gradNormSq_of_energy hφ hE)]
  have hC : 0 ≤ C0 := by nlinarith [sq_nonneg K1, sq_nonneg K2]
  calc
    ∫ x, hessSq (cutoffMul R φ) x ∂volume ≤
        ∫ x, C0 * (φ x ^ 2 + gradNormSq φ x + hessSq φ x) ∂volume := hmono
    _ = C0 * (∫ x, φ x ^ 2 ∂volume + ∫ x, gradNormSq φ x ∂volume +
            ∫ x, hessSq φ x ∂volume) := hrhs
    _ ≤ C0 * (3 * (energyR 2 φ).toReal) :=
        mul_le_mul_of_nonneg_left (integral_three_energy hφ hE) hC
    _ = C0 * 3 * (energyR 2 φ).toReal := by ring
    _ = (36 * K2 ^ 2 + 24 * K1 ^ 2 + 4) * 3 * (energyR 2 φ).toReal := rfl

lemma integral_gradNormSq_sq_cutoffMul_le {R : ℝ} (hR : 1 ≤ R) {φ : T3 → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hE : energyR 2 φ < ⊤) {M : ℝ}
    (hM : ∀ x, |φ x| ≤ M) {K1 K2 : ℝ} (hK1nn : 0 ≤ K1) (hK2nn : 0 ≤ K2)
    (hK1 : ∀ (i : Fin 3) (x : T3), |partiali (cutoff R) i x| ≤ |R⁻¹| * K1)
    (hK2 : ∀ (i j : Fin 3) (x : T3),
      |partiali (partiali (cutoff R) i) j x| ≤ |R⁻¹| * |R⁻¹| * K2) :
    ∫ x, gradNormSq (cutoffMul R φ) x ^ 2 ∂volume ≤
      (Real.sqrt 3 + 2) ^ 2 * M ^ 2 *
        ((36 * K2 ^ 2 + 24 * K1 ^ 2 + 4) * 3 * (energyR 2 φ).toReal) := by
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  have hcs := hasCompactSupport_cutoffMul (φ := φ) (ne_of_gt hR0)
  have hbound := integral_gradNormSq_sq_le_of_hasCompactSupport
    (contDiff_cutoffMul hφ) hcs (abs_cutoffMul_le hM)
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (integral_hessSq_cutoffMul_le hR hφ hE hK1nn hK2nn hK1 hK2)
    (mul_nonneg (sq_nonneg _) (sq_nonneg M)))

/-- L¹ bound on `|∇φ|⁴` via cutoffs and Fatou. Direct IBP on `φ` itself is
not available: `|∇φ|⁴` is not a priori integrable from finite H² energy
plus a sup bound, so `IBPWholeSpace` cannot be applied to `φ`. -/
lemma lintegral_gradNormSq_sq_le_of_energy {φ : T3 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hE : energyR 2 φ < ⊤) {M : ℝ} (hM : ∀ x, |φ x| ≤ M) {K1 K2 : ℝ}
    (hK1nn : 0 ≤ K1) (hK2nn : 0 ≤ K2)
    (hK1b : ∀ y, ‖fderiv ℝ (fun z => (unitBump : T3 → ℝ) z) y‖ ≤ K1)
    (hK2b : ∀ (i j : Fin 3) (y : T3),
      |partiali (partiali (fun z => (unitBump : T3 → ℝ) z) i) j y| ≤ K2) :
    ∫⁻ x, ENNReal.ofReal (gradNormSq φ x ^ 2) ∂volume ≤
      ENNReal.ofReal
        ((Real.sqrt 3 + 2) ^ 2 * M ^ 2 *
          ((36 * K2 ^ 2 + 24 * K1 ^ 2 + 4) * 3 * (energyR 2 φ).toReal)) := by
  set Bound :=
    (Real.sqrt 3 + 2) ^ 2 * M ^ 2 *
      ((36 * K2 ^ 2 + 24 * K1 ^ 2 + 4) * 3 * (energyR 2 φ).toReal)
  have hcut : ∀ n : ℕ,
      ∫ x, gradNormSq (cutoffMul (n + 1 : ℝ) φ) x ^ 2 ∂volume ≤ Bound := by
    intro n
    have hR : (1 : ℝ) ≤ n + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hK1 : ∀ (i : Fin 3) (x : T3),
        |partiali (cutoff (n + 1 : ℝ)) i x| ≤ |(n + 1 : ℝ)⁻¹| * K1 :=
      fun i x => abs_partiali_cutoff_le hK1b i x
    have hK2 : ∀ (i j : Fin 3) (x : T3),
        |partiali (partiali (cutoff (n + 1 : ℝ)) i) j x| ≤
          |(n + 1 : ℝ)⁻¹| * |(n + 1 : ℝ)⁻¹| * K2 :=
      fun i j x => abs_partiali2_cutoff_le hK2b i j x
    exact integral_gradNormSq_sq_cutoffMul_le hR hφ hE hM hK1nn hK2nn hK1 hK2
  have hpt : ∀ x,
      Filter.Tendsto
        (fun n : ℕ => ENNReal.ofReal (gradNormSq (cutoffMul (n + 1 : ℝ) φ) x ^ 2))
        Filter.atTop (nhds (ENNReal.ofReal (gradNormSq φ x ^ 2))) := by
    intro x
    have hev : ∀ᶠ n : ℕ in Filter.atTop,
        ENNReal.ofReal (gradNormSq (cutoffMul (n + 1 : ℝ) φ) x ^ 2) =
          ENNReal.ofReal (gradNormSq φ x ^ 2) := by
      refine Filter.eventually_atTop.mpr ⟨Nat.ceil ‖x‖, fun n hn => ?_⟩
      have hx : ‖x‖ < (n + 1 : ℝ) :=
        (Nat.ceil_le.mp hn).trans_lt (lt_add_one (n : ℝ))
      have hR : (0 : ℝ) < n + 1 := add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one
      rw [gradNormSq_cutoffMul_eq_of_lt hR hx]
    exact tendsto_nhds_of_eventually_eq hev
  have hmeas : ∀ n : ℕ,
      Measurable (fun x =>
        ENNReal.ofReal (gradNormSq (cutoffMul (n + 1 : ℝ) φ) x ^ 2)) := fun n =>
    ((contDiff_gradNormSq (contDiff_cutoffMul (R := (n + 1 : ℝ)) hφ)).continuous.pow 2).measurable.ennreal_ofReal
  have hfatou :=
    lintegral_liminf_le (μ := volume)
      (f := fun n x => ENNReal.ofReal (gradNormSq (cutoffMul (n + 1 : ℝ) φ) x ^ 2))
      hmeas
  have hlimpt : (fun x => Filter.liminf (fun n : ℕ =>
        ENNReal.ofReal (gradNormSq (cutoffMul (n + 1 : ℝ) φ) x ^ 2)) Filter.atTop) =
      fun x => ENNReal.ofReal (gradNormSq φ x ^ 2) :=
    funext fun x => (hpt x).liminf_eq
  have hlin : ∫⁻ x, ENNReal.ofReal (gradNormSq φ x ^ 2) ∂volume ≤
      Filter.liminf (fun n : ℕ =>
        ∫⁻ x, ENNReal.ofReal (gradNormSq (cutoffMul (n + 1 : ℝ) φ) x ^ 2) ∂volume)
        Filter.atTop := by
    simpa [hlimpt] using hfatou
  have hint_eq : ∀ n : ℕ,
      ∫⁻ x, ENNReal.ofReal (gradNormSq (cutoffMul (n + 1 : ℝ) φ) x ^ 2) ∂volume =
        ENNReal.ofReal (∫ x, gradNormSq (cutoffMul (n + 1 : ℝ) φ) x ^ 2 ∂volume) := by
    intro n
    have hR0 : (0 : ℝ) < (n + 1 : ℝ) :=
      add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one
    have hint : Integrable (fun x => gradNormSq (cutoffMul (n + 1 : ℝ) φ) x ^ 2) volume :=
      integrable_gradNormSq_sq (contDiff_cutoffMul hφ)
        (hasCompactSupport_cutoffMul (ne_of_gt hR0))
    exact (ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm
  have hlin_le : Filter.liminf (fun n : ℕ =>
      ∫⁻ x, ENNReal.ofReal (gradNormSq (cutoffMul (n + 1 : ℝ) φ) x ^ 2) ∂volume)
      Filter.atTop ≤ ENNReal.ofReal Bound := by
    have hle : ∀ n : ℕ, ∫⁻ x, ENNReal.ofReal (gradNormSq (cutoffMul (n + 1 : ℝ) φ) x ^ 2)
        ∂volume ≤ ENNReal.ofReal Bound := fun n => by
      rw [hint_eq n]
      exact ENNReal.ofReal_le_ofReal (hcut n)
    have hconst : Filter.liminf (fun _ : ℕ => ENNReal.ofReal Bound) Filter.atTop =
        ENNReal.ofReal Bound := tendsto_const_nhds.liminf_eq
    exact (Filter.liminf_le_liminf (Filter.Eventually.of_forall hle)).trans_eq hconst
  exact hlin.trans hlin_le

lemma integrable_gradNormSq_sq_of_energy {φ : T3 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hE : energyR 2 φ < ⊤) {M : ℝ} (hM : ∀ x, |φ x| ≤ M) {K1 K2 : ℝ}
    (hK1nn : 0 ≤ K1) (hK2nn : 0 ≤ K2)
    (hK1b : ∀ y, ‖fderiv ℝ (fun z => (unitBump : T3 → ℝ) z) y‖ ≤ K1)
    (hK2b : ∀ (i j : Fin 3) (y : T3),
      |partiali (partiali (fun z => (unitBump : T3 → ℝ) z) i) j y| ≤ K2) :
    Integrable (fun x => gradNormSq φ x ^ 2) volume :=
  integrable_of_lintegral_ofReal ((contDiff_gradNormSq hφ).continuous.pow 2)
    (fun _ => sq_nonneg _)
    ((lintegral_gradNormSq_sq_le_of_energy hφ hE hM hK1nn hK2nn hK1b hK2b).trans_lt
      ENNReal.ofReal_lt_top)

lemma integral_gradNormSq_sq_le_of_energy {φ : T3 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hE : energyR 2 φ < ⊤) {M : ℝ} (hM : ∀ x, |φ x| ≤ M) {K1 K2 : ℝ}
    (hK1nn : 0 ≤ K1) (hK2nn : 0 ≤ K2)
    (hK1b : ∀ y, ‖fderiv ℝ (fun z => (unitBump : T3 → ℝ) z) y‖ ≤ K1)
    (hK2b : ∀ (i j : Fin 3) (y : T3),
      |partiali (partiali (fun z => (unitBump : T3 → ℝ) z) i) j y| ≤ K2) :
    ∫ x, gradNormSq φ x ^ 2 ∂volume ≤
      (Real.sqrt 3 + 2) ^ 2 * M ^ 2 *
        ((36 * K2 ^ 2 + 24 * K1 ^ 2 + 4) * 3 * (energyR 2 φ).toReal) := by
  set Bound :=
    (Real.sqrt 3 + 2) ^ 2 * M ^ 2 *
      ((36 * K2 ^ 2 + 24 * K1 ^ 2 + 4) * 3 * (energyR 2 φ).toReal)
  have hM0 : 0 ≤ M := (abs_nonneg (φ 0)).trans (hM 0)
  have hBound : 0 ≤ Bound := by
    dsimp only [Bound]
    have hC : 0 ≤ 36 * K2 ^ 2 + 24 * K1 ^ 2 + 4 := by
      nlinarith [sq_nonneg K1, sq_nonneg K2]
    have hE0 : 0 ≤ (energyR 2 φ).toReal := ENNReal.toReal_nonneg
    refine mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg M)) ?_
    exact mul_nonneg (mul_nonneg hC (by norm_num : (0 : ℝ) ≤ 3)) hE0
  have hint := integrable_gradNormSq_sq_of_energy hφ hE hM hK1nn hK2nn hK1b hK2b
  have hlin := lintegral_gradNormSq_sq_le_of_energy hφ hE hM hK1nn hK2nn hK1b hK2b
  have := integral_le_toReal_of_lintegral hint (fun _ => sq_nonneg _) hlin
    ENNReal.ofReal_ne_top
  rwa [ENNReal.toReal_ofReal hBound] at this

lemma contDiff_dkj {u : VelocityField} (hu : ContDiff ℝ ∞ u) (k j : Fin 3) :
    ContDiff ℝ ∞ (dkj u k j) :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j).contDiff.comp
    ((hu.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const)

lemma abs_dkj_le_gradSup {u : VelocityField} (hu : ContDiff ℝ ∞ u)
    (hE : sobolevEnergy 3 u < ⊤) (k j : Fin 3) (x : T3) :
    |dkj u k j x| ≤ gradSup u := by
  have h1 : |dkj u k j x| ≤ ‖fderiv ℝ u x (EuclideanSpace.single k (1 : ℝ))‖ := by
    simpa [dkj, Real.norm_eq_abs] using
      PiLp.norm_apply_le (fderiv ℝ u x (EuclideanSpace.single k (1 : ℝ))) j
  have h2 : ‖fderiv ℝ u x (EuclideanSpace.single k (1 : ℝ))‖ ≤
      ‖fderiv ℝ u x‖ * ‖EuclideanSpace.single k (1 : ℝ)‖ :=
    (fderiv ℝ u x).le_opNorm _
  have he : ‖EuclideanSpace.single k (1 : ℝ)‖ = 1 := by
    simp [PiLp.norm_single]
  have h3 : ‖fderiv ℝ u x‖ ≤ gradSup u := le_gradSup hu hE x
  nlinarith [norm_nonneg (fderiv ℝ u x)]

lemma wordDeriv_two_eq_partiali_dkj {u : VelocityField} (hu : ContDiff ℝ ∞ u)
    (α : Fin 2 → Fin 3) (j : Fin 3) (x : T3) :
    wordDeriv 2 α u x j = partiali (dkj u (α 1) j) (α 0) x := by
  have hα : α = Fin.snoc (fun _ : Fin 1 => α 0) (α 1) := by
    ext i; fin_cases i <;> simp [Fin.snoc]
  have hiter := iter_dkj hu (α 1) j 1 (fun _ : Fin 1 => α 0) x
  have hL : iteratedFDeriv ℝ 1 (dkj u (α 1) j) x (U (fun _ : Fin 1 => α 0)) =
      partiali (dkj u (α 1) j) (α 0) x := by
    rw [iteratedFDeriv_one_apply, partiali, U]
    rfl
  have hR : iteratedFDeriv ℝ 2 u x (U (Fin.snoc (fun _ : Fin 1 => α 0) (α 1))) j =
      wordDeriv 2 α u x j := by
    unfold wordDeriv U
    rw [← hα]
  exact hR.symm.trans (hiter.symm.trans hL)

lemma abs_partiali_le_sqrt_gradNormSq {φ : T3 → ℝ} (i : Fin 3) (x : T3) :
    |partiali φ i x| ≤ Real.sqrt (gradNormSq φ x) := by
  have hnn : 0 ≤ gradNormSq φ x := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have : partiali φ i x ^ 2 ≤ gradNormSq φ x :=
    Finset.single_le_sum (f := fun i : Fin 3 => partiali φ i x ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  exact (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    (by simpa [sq_abs, Real.sq_sqrt hnn] using this)

lemma pow_four_partiali_le {φ : T3 → ℝ} (i : Fin 3) (x : T3) :
    partiali φ i x ^ (4 : ℕ) ≤ gradNormSq φ x ^ 2 := by
  have hle := abs_partiali_le_sqrt_gradNormSq (φ := φ) i x
  have hnn : 0 ≤ gradNormSq φ x := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hpow : |partiali φ i x| ^ 4 ≤ Real.sqrt (gradNormSq φ x) ^ 4 :=
    pow_le_pow_left₀ (abs_nonneg _) hle 4
  have hr : Real.sqrt (gradNormSq φ x) ^ 4 = gradNormSq φ x ^ 2 := by
    have hs := Real.sq_sqrt hnn
    calc
      Real.sqrt (gradNormSq φ x) ^ 4
          = (Real.sqrt (gradNormSq φ x) ^ 2) ^ 2 := by ring
      _ = gradNormSq φ x ^ 2 := by simp [hs]
  have habs : |partiali φ i x| ^ 4 = partiali φ i x ^ 4 := by
    simp [pow_succ, pow_zero, sq_abs, mul_assoc, pow_two]
  exact (habs.symm.trans_le hpow).trans_eq hr

lemma euclidean_norm_sq (v : T3) : ‖v‖ ^ 2 = ∑ i : Fin 3, v i ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Real.norm_eq_abs, sq_abs]

lemma norm_pow_four_le_three_sum (v : T3) :
    ‖v‖ ^ (4 : ℕ) ≤ 3 * ∑ j : Fin 3, v j ^ (4 : ℕ) := by
  have hsq := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (Fin 3))) (f := fun j : Fin 3 => v j ^ 2)
  have hcard : ((Finset.univ : Finset (Fin 3)).card : ℝ) = 3 := by simp
  calc
    ‖v‖ ^ (4 : ℕ) = (‖v‖ ^ 2) ^ 2 := by ring
    _ = (∑ j : Fin 3, v j ^ 2) ^ 2 := by rw [euclidean_norm_sq]
    _ ≤ ((Finset.univ : Finset (Fin 3)).card : ℝ) *
          ∑ j : Fin 3, (v j ^ 2) ^ 2 := hsq
    _ = 3 * ∑ j : Fin 3, (v j ^ 2) ^ 2 := by rw [hcard]
    _ = 3 * ∑ j : Fin 3, v j ^ (4 : ℕ) := by
        congr 1
        exact Finset.sum_congr rfl fun j _ => by ring

lemma wordDeriv_two_component_pow_four_le {u : VelocityField} (hu : ContDiff ℝ ∞ u)
    (α : Fin 2 → Fin 3) (j : Fin 3) (x : T3) :
    (wordDeriv 2 α u x j) ^ (4 : ℕ) ≤ gradNormSq (dkj u (α 1) j) x ^ 2 := by
  rw [wordDeriv_two_eq_partiali_dkj hu α j x]
  exact pow_four_partiali_le (α 0) x

lemma sum_gradNormSq_word_reindex (u : VelocityField) (x : T3) :
    ∑ α : Fin 2 → Fin 3, ∑ j : Fin 3, gradNormSq (dkj u (α 1) j) x ^ 2 =
      3 * ∑ k : Fin 3, ∑ j : Fin 3, gradNormSq (dkj u k j) x ^ 2 := by
  have h1 : ∑ α : Fin 2 → Fin 3, ∑ j : Fin 3, gradNormSq (dkj u (α 1) j) x ^ 2 =
      ∑ p : Fin 3 × Fin 3, ∑ j : Fin 3, gradNormSq (dkj u p.2 j) x ^ 2 := by
    refine Fintype.sum_equiv (piFinTwoEquiv fun _ : Fin 2 => Fin 3)
      (fun α => ∑ j : Fin 3, gradNormSq (dkj u (α 1) j) x ^ 2)
      (fun p => ∑ j : Fin 3, gradNormSq (dkj u p.2 j) x ^ 2) ?_
    intro α
    have hp : (piFinTwoEquiv fun _ : Fin 2 => Fin 3) α = (α 0, α 1) := rfl
    simp [hp]
  have h2 : ∑ p : Fin 3 × Fin 3, ∑ j : Fin 3, gradNormSq (dkj u p.2 j) x ^ 2 =
      ∑ a0 : Fin 3, ∑ a1 : Fin 3, ∑ j : Fin 3, gradNormSq (dkj u a1 j) x ^ 2 :=
    (sum_sum_eq_sum_prod (fun a0 a1 =>
      ∑ j : Fin 3, gradNormSq (dkj u a1 j) x ^ 2)).symm
  have h3 : ∑ a0 : Fin 3, ∑ a1 : Fin 3, ∑ j : Fin 3, gradNormSq (dkj u a1 j) x ^ 2 =
      3 * ∑ k : Fin 3, ∑ j : Fin 3, gradNormSq (dkj u k j) x ^ 2 := by
    have hswap :
        ∑ a0 : Fin 3, ∑ a1 : Fin 3, ∑ j : Fin 3, gradNormSq (dkj u a1 j) x ^ 2 =
          ∑ a1 : Fin 3, ∑ a0 : Fin 3, ∑ j : Fin 3, gradNormSq (dkj u a1 j) x ^ 2 :=
      Finset.sum_comm
    have hconst :
        ∑ a1 : Fin 3, ∑ a0 : Fin 3, ∑ j : Fin 3, gradNormSq (dkj u a1 j) x ^ 2 =
          ∑ a1 : Fin 3, 3 * ∑ j : Fin 3, gradNormSq (dkj u a1 j) x ^ 2 := by
      refine Finset.sum_congr rfl fun a1 _ => ?_
      simp [Finset.sum_const, Fintype.card_fin]
    have hmul :
        ∑ a1 : Fin 3, 3 * ∑ j : Fin 3, gradNormSq (dkj u a1 j) x ^ 2 =
          3 * ∑ k : Fin 3, ∑ j : Fin 3, gradNormSq (dkj u k j) x ^ 2 :=
      (Finset.mul_sum _ _ _).symm
    exact (hswap.trans hconst).trans hmul
  exact (h1.trans h2).trans h3

lemma sum_wordDeriv_two_pow_four_le (u : VelocityField) (hu : ContDiff ℝ ∞ u)
    (x : T3) :
    ∑ α : Fin 2 → Fin 3, ‖wordDeriv 2 α u x‖ ^ (4 : ℕ) ≤
      9 * ∑ k : Fin 3, ∑ j : Fin 3, gradNormSq (dkj u k j) x ^ 2 := by
  have hsumα :
      ∑ α : Fin 2 → Fin 3, ‖wordDeriv 2 α u x‖ ^ (4 : ℕ) ≤
        3 * ∑ α : Fin 2 → Fin 3, ∑ j : Fin 3, (wordDeriv 2 α u x j) ^ (4 : ℕ) := by
    have := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 2 → Fin 3)))
      (fun α _ => norm_pow_four_le_three_sum (wordDeriv 2 α u x))
    exact this.trans_eq (Finset.mul_sum _ _ _).symm
  have hsumcomp :
      ∑ α : Fin 2 → Fin 3, ∑ j : Fin 3, (wordDeriv 2 α u x j) ^ (4 : ℕ) ≤
        ∑ α : Fin 2 → Fin 3, ∑ j : Fin 3, gradNormSq (dkj u (α 1) j) x ^ 2 :=
    Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun j _ =>
      wordDeriv_two_component_pow_four_le hu α j x
  calc
    ∑ α : Fin 2 → Fin 3, ‖wordDeriv 2 α u x‖ ^ (4 : ℕ)
        ≤ 3 * ∑ α : Fin 2 → Fin 3, ∑ j : Fin 3, (wordDeriv 2 α u x j) ^ (4 : ℕ) :=
          hsumα
    _ ≤ 3 * ∑ α : Fin 2 → Fin 3, ∑ j : Fin 3, gradNormSq (dkj u (α 1) j) x ^ 2 :=
          mul_le_mul_of_nonneg_left hsumcomp (by norm_num)
    _ = 3 * (3 * ∑ k : Fin 3, ∑ j : Fin 3, gradNormSq (dkj u k j) x ^ 2) := by
          rw [sum_gradNormSq_word_reindex]
    _ = 9 * ∑ k : Fin 3, ∑ j : Fin 3, gradNormSq (dkj u k j) x ^ 2 := by ring

/-- **Gagliardo–Nirenberg interpolation on ℝ³.**

There is a constant `C ≥ 0` such that for every smooth field with finite
H³ energy,
`∑_{α : Fin 2 → Fin 3} ∫ ‖wordDeriv 2 α u‖⁴ ≤ C ‖∇u‖_∞² ‖u‖²_{H³}`.

The identity `∫ |∇φ|⁴ = -∫ φ ∑ᵢ ∂ᵢ(∂ᵢφ · |∇φ|²)` is applied to the
compactly supported cutoffs `χ_R φ`, a uniform bound on `∫ |Hess(χ_R φ)|²`
is taken from the H² energy of `φ`, and the `R → ∞` limit is Fatou.
Direct IBP on `φ` itself is not available: `|∇φ|⁴` is not a priori
integrable from finite H² energy plus a sup bound. -/
def H3GagliardoNirenberg : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : VelocityField),
    ContDiff ℝ ∞ u →
    sobolevEnergy 3 u < ⊤ →
    ∑ α : Fin 2 → Fin 3,
        ∫ x, ‖wordDeriv 2 α u x‖ ^ (4 : ℕ) ∂volume ≤
      C * gradSup u ^ 2 * hsSq 3 u

set_option maxHeartbeats 800000 in
theorem h3GagliardoNirenberg : H3GagliardoNirenberg := by
  obtain ⟨K1, hK1nn, hK1b⟩ := exists_bound_unitBump_fderiv
  obtain ⟨K2, hK2nn, hK2b⟩ := exists_bound_unitBump_partiali2
  let C0 : ℝ := 36 * K2 ^ 2 + 24 * K1 ^ 2 + 4
  let C1 : ℝ := (Real.sqrt 3 + 2) ^ 2 * (C0 * 3)
  let C : ℝ := 81 * C1
  have hC0 : 0 ≤ C0 := by nlinarith [sq_nonneg K1, sq_nonneg K2]
  have hC1 : 0 ≤ C1 := mul_nonneg (sq_nonneg _) (mul_nonneg hC0 (by norm_num))
  have hC : 0 ≤ C := mul_nonneg (by norm_num) hC1
  refine ⟨C, hC, ?_⟩
  intro u hu hE
  have hgs0 : 0 ≤ gradSup u :=
    (norm_nonneg (fderiv ℝ u 0)).trans (le_gradSup hu hE 0)
  have hscalar : ∀ (k j : Fin 3),
      ∫ x, gradNormSq (dkj u k j) x ^ 2 ∂volume ≤
        C1 * gradSup u ^ 2 * (energyR 2 (dkj u k j)).toReal := by
    intro k j
    have hφ := contDiff_dkj hu k j
    have hEd : energyR 2 (dkj u k j) < ⊤ :=
      (energyR_dkj_le hu k j).trans_lt hE
    have hM : ∀ x, |dkj u k j x| ≤ gradSup u := fun x =>
      abs_dkj_le_gradSup hu hE k j x
    have hle := integral_gradNormSq_sq_le_of_energy hφ hEd hM hK1nn hK2nn hK1b hK2b
    have hrw : (Real.sqrt 3 + 2) ^ 2 * gradSup u ^ 2 *
        ((36 * K2 ^ 2 + 24 * K1 ^ 2 + 4) * 3 * (energyR 2 (dkj u k j)).toReal) =
      C1 * gradSup u ^ 2 * (energyR 2 (dkj u k j)).toReal := by
      simp [C1, C0]; ring
    exact hle.trans_eq hrw
  have hterm : ∀ (k j : Fin 3),
      ∫ x, gradNormSq (dkj u k j) x ^ 2 ∂volume ≤
        C1 * gradSup u ^ 2 * hsSq 3 u := by
    intro k j
    have hEd : energyR 2 (dkj u k j) < ⊤ :=
      (energyR_dkj_le hu k j).trans_lt hE
    have hmono : (energyR 2 (dkj u k j)).toReal ≤ hsSq 3 u :=
      ENNReal.toReal_mono hE.ne (energyR_dkj_le hu k j)
    have hfac : 0 ≤ C1 * gradSup u ^ 2 := mul_nonneg hC1 (sq_nonneg _)
    exact (hscalar k j).trans (mul_le_mul_of_nonneg_left hmono hfac)
  have hintkj : ∀ (k j : Fin 3),
      Integrable (fun x => gradNormSq (dkj u k j) x ^ 2) volume := fun k j =>
    integrable_gradNormSq_sq_of_energy (contDiff_dkj hu k j)
      ((energyR_dkj_le hu k j).trans_lt hE)
      (fun x => abs_dkj_le_gradSup hu hE k j x) hK1nn hK2nn hK1b hK2b
  have hint_sum : Integrable (fun x =>
      ∑ k : Fin 3, ∑ j : Fin 3, gradNormSq (dkj u k j) x ^ 2) volume := by
    have h1 : Integrable (fun x =>
        ∑ p : Fin 3 × Fin 3, gradNormSq (dkj u p.1 p.2) x ^ 2) volume :=
      integrable_finset_sum (Finset.univ : Finset (Fin 3 × Fin 3))
        fun p _ => hintkj p.1 p.2
    have heq : (fun x => ∑ k : Fin 3, ∑ j : Fin 3, gradNormSq (dkj u k j) x ^ 2) =
        fun x => ∑ p : Fin 3 × Fin 3, gradNormSq (dkj u p.1 p.2) x ^ 2 := by
      funext x
      exact sum_sum_eq_sum_prod (fun k j => gradNormSq (dkj u k j) x ^ 2)
    rwa [heq]
  have hintα : ∀ α : Fin 2 → Fin 3,
      Integrable (fun x => ‖wordDeriv 2 α u x‖ ^ (4 : ℕ)) volume := by
    intro α
    have hcont : Continuous (fun x => ‖wordDeriv 2 α u x‖ ^ (4 : ℕ)) :=
      (contDiff_wordDeriv (k := 2) α hu).continuous.norm.pow 4
    have hnn : 0 ≤ fun x => ‖wordDeriv 2 α u x‖ ^ (4 : ℕ) := fun x =>
      pow_nonneg (norm_nonneg _) _
    have hle : ∀ x, ‖wordDeriv 2 α u x‖ ^ (4 : ℕ) ≤
        9 * ∑ k : Fin 3, ∑ j : Fin 3, gradNormSq (dkj u k j) x ^ 2 := fun x =>
      (Finset.single_le_sum
        (f := fun α : Fin 2 → Fin 3 => ‖wordDeriv 2 α u x‖ ^ (4 : ℕ))
        (fun _ _ => pow_nonneg (norm_nonneg _) _) (Finset.mem_univ α)).trans
        (sum_wordDeriv_two_pow_four_le u hu x)
    exact (hint_sum.const_mul 9).mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs, abs_of_nonneg (hnn x)] using hle x)
  have hsum_int :
      ∫ x, ∑ α : Fin 2 → Fin 3, ‖wordDeriv 2 α u x‖ ^ (4 : ℕ) ∂volume =
        ∑ α : Fin 2 → Fin 3, ∫ x, ‖wordDeriv 2 α u x‖ ^ (4 : ℕ) ∂volume :=
    integral_finset_sum (Finset.univ : Finset (Fin 2 → Fin 3))
      (fun α _ => hintα α)
  have hnn_sum : ∀ x, 0 ≤ ∑ α : Fin 2 → Fin 3, ‖wordDeriv 2 α u x‖ ^ (4 : ℕ) :=
    fun x => Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _
  have hmono := integral_mono_of_nonneg (Filter.Eventually.of_forall hnn_sum)
    (hint_sum.const_mul 9)
    (Filter.Eventually.of_forall fun x => sum_wordDeriv_two_pow_four_le u hu x)
  have hrhs :
      ∫ x, 9 * ∑ k : Fin 3, ∑ j : Fin 3, gradNormSq (dkj u k j) x ^ 2 ∂volume =
        9 * ∑ k : Fin 3, ∑ j : Fin 3,
          ∫ x, gradNormSq (dkj u k j) x ^ 2 ∂volume := by
    have hprod : ∫ x, ∑ k : Fin 3, ∑ j : Fin 3, gradNormSq (dkj u k j) x ^ 2 ∂volume =
        ∑ k : Fin 3, ∑ j : Fin 3, ∫ x, gradNormSq (dkj u k j) x ^ 2 ∂volume := by
      have := integral_finset_sum (Finset.univ : Finset (Fin 3 × Fin 3))
        (fun p _ => hintkj p.1 p.2)
      have heq1 : (fun x => ∑ k : Fin 3, ∑ j : Fin 3, gradNormSq (dkj u k j) x ^ 2) =
          fun x => ∑ p : Fin 3 × Fin 3, gradNormSq (dkj u p.1 p.2) x ^ 2 := by
        funext x
        exact sum_sum_eq_sum_prod (fun k j => gradNormSq (dkj u k j) x ^ 2)
      have heq2 :
          ∑ k : Fin 3, ∑ j : Fin 3, ∫ x, gradNormSq (dkj u k j) x ^ 2 ∂volume =
            ∑ p : Fin 3 × Fin 3, ∫ x, gradNormSq (dkj u p.1 p.2) x ^ 2 ∂volume :=
        sum_sum_eq_sum_prod (fun k j => ∫ x, gradNormSq (dkj u k j) x ^ 2 ∂volume)
      simpa [heq1, heq2] using this
    rw [integral_const_mul, hprod]
  have hsumkj :
      9 * ∑ k : Fin 3, ∑ j : Fin 3,
          ∫ x, gradNormSq (dkj u k j) x ^ 2 ∂volume ≤
        9 * ∑ k : Fin 3, ∑ j : Fin 3, C1 * gradSup u ^ 2 * hsSq 3 u := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun j _ => hterm k j
  have hcount :
      9 * ∑ k : Fin 3, ∑ j : Fin 3, C1 * gradSup u ^ 2 * hsSq 3 u =
        C * gradSup u ^ 2 * hsSq 3 u := by
    have hconst : ∑ k : Fin 3, ∑ j : Fin 3, C1 * gradSup u ^ 2 * hsSq 3 u =
        9 * (C1 * gradSup u ^ 2 * hsSq 3 u) := by
      have : ∑ k : Fin 3, ∑ j : Fin 3, C1 * gradSup u ^ 2 * hsSq 3 u =
          ∑ k : Fin 3, 3 * (C1 * gradSup u ^ 2 * hsSq 3 u) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [Finset.sum_const, Fintype.card_fin]
      rw [this, ← Finset.mul_sum]
      simp [Finset.sum_const, Fintype.card_fin]
      ring
    rw [hconst]
    change 9 * (9 * (C1 * gradSup u ^ 2 * hsSq 3 u)) = C * gradSup u ^ 2 * hsSq 3 u
    simp only [C]
    ring
  calc
    ∑ α : Fin 2 → Fin 3, ∫ x, ‖wordDeriv 2 α u x‖ ^ (4 : ℕ) ∂volume
        = ∫ x, ∑ α : Fin 2 → Fin 3, ‖wordDeriv 2 α u x‖ ^ (4 : ℕ) ∂volume :=
          hsum_int.symm
    _ ≤ ∫ x, 9 * ∑ k : Fin 3, ∑ j : Fin 3, gradNormSq (dkj u k j) x ^ 2 ∂volume :=
          hmono
    _ = 9 * ∑ k : Fin 3, ∑ j : Fin 3,
          ∫ x, gradNormSq (dkj u k j) x ^ 2 ∂volume := hrhs
    _ ≤ 9 * ∑ k : Fin 3, ∑ j : Fin 3, C1 * gradSup u ^ 2 * hsSq 3 u := hsumkj
    _ = C * gradSup u ^ 2 * hsSq 3 u := hcount

#print axioms KatoPonceCommutator.convectiveCommutator_order_one
#print axioms KatoPonceCommutator.norm_convectiveCommutator_order_one
#print axioms KatoPonceCommutator.abs_integral_commutator_order_one
#print axioms KatoPonceCommutator.integral_gradNormSq_sq
#print axioms KatoPonceCommutator.integral_gradNormSq_sq_le_of_hasCompactSupport
#print axioms KatoPonceCommutator.partiali2_cutoff
#print axioms KatoPonceCommutator.h3GagliardoNirenberg

end KatoPonceCommutator
