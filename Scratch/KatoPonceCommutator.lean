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
`|∫ ⟨∂ᵢ u, [∂ᵢ, u·∇]u⟩| ≤ ‖∇u‖_∞ ∫ |∂ᵢ u|²`, and the compact-support
Gagliardo–Nirenberg bound `∫ |∇φ|⁴ ≤ (√3+2)² M² ∫ |Hess φ|²` for
`C^∞` compactly supported scalars with `|φ| ≤ M`, obtained from the
whole-space IBP identity `∫ |∇φ|⁴ = -∫ φ ∑ᵢ ∂ᵢ(∂ᵢφ · |∇φ|²)` followed
by Hölder. Cutoff helpers `χ_R φ` (and bounds on the first and second
partials of the unit bump) are also in place. The order-zero commutator
is already `convectiveCommutator_zero` in `KatoPonce`.

What remains for `H3CommutatorEstimate` itself: extending that GN bound
to every `C^∞` field with only finite H³ energy (named
`H3GagliardoNirenberg` below), the Leibniz expansion and Hölder bounds
for `|α| = 2, 3` (the `|α| = 3`, `|β| = 2` term is the one that needs
GN), and the assembly. A Fourier-side product estimate would bound by
`‖û‖` norms, which do not imply the `‖∇u‖_∞` form, so it is not used
here. (`GradBound` already gives `‖∇u‖_∞ ≲ ‖u‖_{H³}` and `BddAbove`,
which we do use.)

The general GN interpolation still needs a cutoff or a direct
integrable-IBP justification on ℝ³; `ContDiff ∞` +
`sobolevEnergy 3 u < ⊤` does not by itself make `|∇φ|⁴` integrable.
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

/-- **Gagliardo–Nirenberg interpolation on ℝ³.**

There is a constant `C ≥ 0` such that for every smooth field with finite
H³ energy, every first-derivative component `φ = ∂_k uⱼ` satisfies
`∫ |∇φ|⁴ ≤ C ‖∇u‖_∞² ∫ |D² φ|²`, or equivalently (summing components)
`‖∂²u‖₄² ≤ C ‖∇u‖_∞ ‖u‖_{H³}`.

This is the standard IBP identity
`∫ |∇φ|⁴ = -∫ φ (Δφ |∇φ|² + 2 ∇φ · (Hess φ ∇φ))` followed by Hölder,
which is justified for compactly supported `φ` (or under a vanishing-flux
hypothesis). Extending it to every `C^∞` field with only finite H³ energy
requires a cutoff `χ_R φ` and a limit `R → ∞`, which is not formalized
here. This `Prop` is not used to weaken `H3CommutatorEstimate`. -/
def H3GagliardoNirenberg : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : VelocityField),
    ContDiff ℝ ∞ u →
    sobolevEnergy 3 u < ⊤ →
    ∑ α : Fin 2 → Fin 3,
        ∫ x, ‖wordDeriv 2 α u x‖ ^ (4 : ℕ) ∂volume ≤
      C * gradSup u ^ 2 * hsSq 3 u

#print axioms KatoPonceCommutator.convectiveCommutator_order_one
#print axioms KatoPonceCommutator.norm_convectiveCommutator_order_one
#print axioms KatoPonceCommutator.abs_integral_commutator_order_one
#print axioms KatoPonceCommutator.integral_gradNormSq_sq
#print axioms KatoPonceCommutator.integral_gradNormSq_sq_le_of_hasCompactSupport
#print axioms KatoPonceCommutator.partiali2_cutoff

end KatoPonceCommutator
