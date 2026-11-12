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

`H3GagliardoNirenberg` is proved above, as is the `|α| = 2` Leibniz
expansion and its `L²` pairing bound. The `|α| = 3` Leibniz expansion,
Hölder/`H3GagliardoNirenberg` bound (needed for the `|β| = 2` terms),
and the assembly of `H3CommutatorEstimate` are carried out below. A Fourier-side product estimate
would bound by `‖û‖` norms, which do not imply the `‖∇u‖_∞` form, so it
is not used here. (`GradBound` already gives `‖∇u‖_∞ ≲ ‖u‖_{H³}` and
`BddAbove`, which we do use.)

The statement of `H3CommutatorEstimate` is not weakened; it remains a
named `Prop` in `KatoPonce.lean`. Once `h3CommutatorEstimate` is proved,
a corollary in this file discharges that hypothesis from
`katoPonce_h3_energy`.

Nothing in this file is a `sorry`, a custom axiom, or an `opaque` trick.
-/

open MeasureTheory hiding volume
open NavierStokes3D FrohmanianTether RepairedTether Set
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

/-! ## Leibniz expansion of the convective commutator at order 2 and 3 -/

lemma mul_le_sq_add_sq (a b : ℝ) : a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

lemma mul_mul_le_sq_add_pow_four (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a * b * c ≤ a ^ 2 / 2 + b ^ 4 / 4 + c ^ 4 / 4 := by
  have h1 : a * (b * c) ≤ a ^ 2 / 2 + (b * c) ^ 2 / 2 := by
    nlinarith [sq_nonneg (a - b * c)]
  have h2 : (b * c) ^ 2 ≤ (b ^ 4 + c ^ 4) / 2 := by
    nlinarith [sq_nonneg (b ^ 2 - c ^ 2)]
  nlinarith

/-- First-order product rule: `∂ᵢ((u·∇)v) = (∂ᵢ u · ∇)v + (u·∇)(∂ᵢ v)`. -/
lemma convective_leibniz_one {u v : VelocityField}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (α : Fin 1 → Fin 3) (x : T3) :
    wordDeriv 1 α (convective u v) x =
      convective (wordDeriv 1 α u) v x + convective u (wordDeriv 1 α v) x := by
  set evec : T3 := EuclideanSpace.single (α 0) (1 : ℝ)
  have huD := differentiable_of_infty hu
  have hvD := differentiable_of_infty hv
  have hDv := differentiable_fderiv_of_infty hv
  have hprod := fderiv_clm_apply (c := fderiv ℝ v) (u := u) (hDv x) (huD x)
  have hwd : wordDeriv 1 α (convective u v) x =
      fderiv ℝ (fun y => (fderiv ℝ v y) (u y)) x evec := by
    rw [wordDeriv_one]; rfl
  have hL : fderiv ℝ (fun y => (fderiv ℝ v y) evec) x (u x) =
      (fderiv ℝ (fderiv ℝ v) x (u x)) evec := by
    let L : (T3 →L[ℝ] T3) →L[ℝ] T3 :=
      ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin 3)) evec
    have hcomp : (fun y => (fderiv ℝ v y) evec) = ⇑L ∘ fderiv ℝ v := rfl
    rw [hcomp, fderiv_comp (f := fderiv ℝ v) (g := ⇑L)
      (x := x) L.differentiableAt (hDv x), ContinuousLinearMap.fderiv]
    rfl
  have hsym :
      (fderiv ℝ (fderiv ℝ v) x (u x)) evec =
        (fderiv ℝ (fderiv ℝ v) x evec) (u x) :=
    second_derivative_symmetric (fun y => (hvD y).hasFDerivAt)
      ((hDv x).hasFDerivAt) (u x) evec
  have hwd_u : wordDeriv 1 α u = fun y => fderiv ℝ u y evec := by
    funext y; exact wordDeriv_one α u y
  have hwd_v : wordDeriv 1 α v = fun y => fderiv ℝ v y evec := by
    funext y; exact wordDeriv_one α v y
  have htr : convective u (wordDeriv 1 α v) x =
      (fderiv ℝ (fderiv ℝ v) x (u x)) evec := by
    simp only [convective, hwd_v]
    exact hL
  calc
    wordDeriv 1 α (convective u v) x
        = fderiv ℝ (fun y => (fderiv ℝ v y) (u y)) x evec := hwd
    _ = (fderiv ℝ v x) (fderiv ℝ u x evec)
          + (fderiv ℝ (fderiv ℝ v) x evec) (u x) := by
        rw [hprod, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.flip_apply]
    _ = convective (wordDeriv 1 α u) v x
          + convective u (wordDeriv 1 α v) x := by
        simp only [convective, hwd_u, hwd_v, hL]
        rw [hsym]

/-- `∂ᵢ(∂^α u)` as a length-`(k+1)` word, new index applied last. -/
lemma wordDeriv_cons {k : ℕ} (i : Fin 3) (α : Fin k → Fin 3) {f : VelocityField}
    (hf : ContDiff ℝ ∞ f) (x : T3) :
    wordDeriv (k + 1) (Fin.cons i α) f x =
      fderiv ℝ (wordDeriv k α f) x (EuclideanSpace.single i (1 : ℝ)) := by
  simpa [Fin.tail_cons] using
    congrFun (wordDeriv_succ (k := k) (Fin.cons i α) (f := f) hf) x

/-- `‖∂ᵢ u(x)‖ ≤ ‖∇u(x)‖`. -/
lemma norm_wordDeriv_one_le (α : Fin 1 → Fin 3) (u : VelocityField) (x : T3) :
    ‖wordDeriv 1 α u x‖ ≤ ‖fderiv ℝ u x‖ := by
  rw [wordDeriv_one]
  have h := (fderiv ℝ u x).le_opNorm (EuclideanSpace.single (α 0) (1 : ℝ))
  have he : ‖EuclideanSpace.single (α 0) (1 : ℝ)‖ = 1 := by
    simp [PiLp.norm_single]
  simpa [he] using h

lemma opNorm_fderiv_wordDeriv_one_le {u : VelocityField} (hu : ContDiff ℝ ∞ u)
    (α : Fin 1 → Fin 3) (x : T3) :
    ‖fderiv ℝ (wordDeriv 1 α u) x‖ ≤
      ∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i α) u x‖ := by
  have hle := GradBound.norm_clm_le (fderiv ℝ (wordDeriv 1 α u) x)
  refine hle.trans (Finset.sum_le_sum fun i _ => ?_)
  exact le_of_eq (congrArg norm (wordDeriv_cons i α hu x).symm)

lemma opNorm_fderiv_wordDeriv_two_le {u : VelocityField} (hu : ContDiff ℝ ∞ u)
    (α : Fin 2 → Fin 3) (x : T3) :
    ‖fderiv ℝ (wordDeriv 2 α u) x‖ ≤
      ∑ i : Fin 3, ‖wordDeriv 3 (Fin.cons i α) u x‖ := by
  have hle := GradBound.norm_clm_le (fderiv ℝ (wordDeriv 2 α u) x)
  refine hle.trans (Finset.sum_le_sum fun i _ => ?_)
  exact le_of_eq (congrArg norm (wordDeriv_cons i α hu x).symm)

lemma integral_wordDeriv_sq_le {f : VelocityField} (hf : ContDiff ℝ ∞ f)
    (hE : sobolevEnergy 3 f < ⊤) {k : ℕ} (hk : k ≤ 3) (α : Fin k → Fin 3) :
    ∫ x, ‖wordDeriv k α f x‖ ^ 2 ∂volume ≤ hsSq 3 f := by
  have hint := integrable_wordDeriv_sq hf hE hk α
  have heq : ∫⁻ x, ENNReal.ofReal (‖wordDeriv k α f x‖ ^ 2) ∂volume =
      ∫⁻ x, ‖wordDeriv k α f x‖ₑ ^ 2 :=
    lintegral_congr fun x => by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  exact integral_le_toReal_of_lintegral hint (fun _ => sq_nonneg _)
    (heq.trans_le (lintegral_wordDeriv_sq_le 3 f hk α)) hE.ne

lemma abs_inner_convective_le {v wvec f : VelocityField} (x : T3)
    (hf : DifferentiableAt ℝ f x) :
    |inner ℝ (v x) (convective wvec f x)| ≤
      ‖v x‖ * ‖fderiv ℝ f x‖ * ‖wvec x‖ := by
  have h1 := abs_real_inner_le_norm (v x) (convective wvec f x)
  have h2 := convective_norm_le wvec f x hf
  nlinarith [norm_nonneg (v x), norm_nonneg (fderiv ℝ f x),
    norm_nonneg (wvec x), norm_nonneg (convective wvec f x)]

/-- Four-term Leibniz expansion of `∂ᵢ∂ⱼ((u·∇)v)`. -/
lemma wordDeriv_convective_order_two {u v : VelocityField}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (α : Fin 2 → Fin 3) (x : T3) :
    wordDeriv 2 α (convective u v) x =
      convective (wordDeriv 2 α u) v x
        + convective (wordDeriv 1 (Fin.tail α) u)
            (wordDeriv 1 (fun _ : Fin 1 => α 0) v) x
        + convective (wordDeriv 1 (fun _ : Fin 1 => α 0) u)
            (wordDeriv 1 (Fin.tail α) v) x
        + convective u (wordDeriv 2 α v) x := by
  have hconv : ContDiff ℝ ∞ (convective u v) := contDiff_convective hu hv
  have hsucc := wordDeriv_succ (k := 1) α (f := convective u v) hconv
  have hone : wordDeriv 1 (Fin.tail α) (convective u v) =
      fun y => convective (wordDeriv 1 (Fin.tail α) u) v y
        + convective u (wordDeriv 1 (Fin.tail α) v) y := by
    funext y; exact convective_leibniz_one hu hv (Fin.tail α) y
  have hp : ContDiff ℝ ∞ (convective (wordDeriv 1 (Fin.tail α) u) v) :=
    contDiff_convective (contDiff_wordDeriv (Fin.tail α) hu) hv
  have hq : ContDiff ℝ ∞ (convective u (wordDeriv 1 (Fin.tail α) v)) :=
    contDiff_convective hu (contDiff_wordDeriv (Fin.tail α) hv)
  have hadd :
      wordDeriv 2 α (convective u v) x =
        wordDeriv 1 (fun _ : Fin 1 => α 0)
            (convective (wordDeriv 1 (Fin.tail α) u) v) x
          + wordDeriv 1 (fun _ : Fin 1 => α 0)
            (convective u (wordDeriv 1 (Fin.tail α) v)) x := by
    have hx : wordDeriv 2 α (convective u v) x =
        fderiv ℝ (wordDeriv 1 (Fin.tail α) (convective u v)) x
          (EuclideanSpace.single (α 0) (1 : ℝ)) := congrFun hsucc x
    rw [hx, hone, fderiv_fun_add (hp.differentiable (by simp) x)
      (hq.differentiable (by simp) x)]
    simp [wordDeriv_one, ContinuousLinearMap.add_apply]
  have h1 := convective_leibniz_one
    (contDiff_wordDeriv (Fin.tail α) hu) hv (fun _ : Fin 1 => α 0) x
  have h2 := convective_leibniz_one hu
    (contDiff_wordDeriv (Fin.tail α) hv) (fun _ : Fin 1 => α 0) x
  have hidU : wordDeriv 1 (fun _ : Fin 1 => α 0) (wordDeriv 1 (Fin.tail α) u) =
      wordDeriv 2 α u := by
    funext y
    simpa [wordDeriv_one] using
      (congrFun (wordDeriv_succ (k := 1) α (f := u) hu) y).symm
  have hidV : wordDeriv 1 (fun _ : Fin 1 => α 0) (wordDeriv 1 (Fin.tail α) v) =
      wordDeriv 2 α v := by
    funext y
    simpa [wordDeriv_one] using
      (congrFun (wordDeriv_succ (k := 1) α (f := v) hv) y).symm
  rw [hadd, h1, h2, hidU, hidV]
  abel

/-- `[∂ᵢ∂ⱼ, u·∇]u = (∂ᵢ∂ⱼ u · ∇)u + (∂ⱼ u · ∇)(∂ᵢ u) + (∂ᵢ u · ∇)(∂ⱼ u)`. -/
lemma convectiveCommutator_order_two {u : VelocityField} (hu : ContDiff ℝ ∞ u)
    (α : Fin 2 → Fin 3) (x : T3) :
    convectiveCommutator 2 α u x =
      convective (wordDeriv 2 α u) u x
        + convective (wordDeriv 1 (Fin.tail α) u)
            (wordDeriv 1 (fun _ : Fin 1 => α 0) u) x
        + convective (wordDeriv 1 (fun _ : Fin 1 => α 0) u)
            (wordDeriv 1 (Fin.tail α) u) x := by
  have h := wordDeriv_convective_order_two hu hu α x
  simp only [convectiveCommutator, h]
  abel

/-- Pointwise bound for the order-two pairing, with a uniform `gradSup` factor
and a sum of `H²` squares. The coefficient `10` absorbs the two
`a S ≤ a² + 3 ∑ b²` estimates together with the `(∂²u · ∇)u` term. -/
lemma abs_pairing_commutator_order_two_le {u : VelocityField}
    (hu : ContDiff ℝ ∞ u) (hE : sobolevEnergy 3 u < ⊤)
    (α : Fin 2 → Fin 3) (x : T3) :
    |inner ℝ (wordDeriv 2 α u x) (convectiveCommutator 2 α u x)| ≤
      gradSup u *
        (10 * ‖wordDeriv 2 α u x‖ ^ 2 +
          3 * ∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i (fun _ : Fin 1 => α 0)) u x‖ ^ 2 +
          3 * ∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i (Fin.tail α)) u x‖ ^ 2) := by
  have hx := convectiveCommutator_order_two hu α x
  have hd_u : DifferentiableAt ℝ u x := differentiable_of_infty hu x
  have hd_i : DifferentiableAt ℝ (wordDeriv 1 (fun _ : Fin 1 => α 0) u) x :=
    (contDiff_wordDeriv (k := 1) (fun _ : Fin 1 => α 0) hu).differentiable (by simp) x
  have hd_j : DifferentiableAt ℝ (wordDeriv 1 (Fin.tail α) u) x :=
    (contDiff_wordDeriv (k := 1) (Fin.tail α) hu).differentiable (by simp) x
  have hgs := le_gradSup hu hE x
  have hgs0 : 0 ≤ gradSup u :=
    (norm_nonneg (fderiv ℝ u 0)).trans (le_gradSup hu hE 0)
  have hsplit :
      |inner ℝ (wordDeriv 2 α u x) (convectiveCommutator 2 α u x)| ≤
        |inner ℝ (wordDeriv 2 α u x) (convective (wordDeriv 2 α u) u x)| +
          |inner ℝ (wordDeriv 2 α u x)
            (convective (wordDeriv 1 (Fin.tail α) u)
              (wordDeriv 1 (fun _ : Fin 1 => α 0) u) x)| +
          |inner ℝ (wordDeriv 2 α u x)
            (convective (wordDeriv 1 (fun _ : Fin 1 => α 0) u)
              (wordDeriv 1 (Fin.tail α) u) x)| := by
    rw [hx, inner_add_right, inner_add_right]
    have habs1 := abs_add_le
      (inner ℝ (wordDeriv 2 α u x) (convective (wordDeriv 2 α u) u x) +
        inner ℝ (wordDeriv 2 α u x)
          (convective (wordDeriv 1 (Fin.tail α) u)
            (wordDeriv 1 (fun _ : Fin 1 => α 0) u) x))
      (inner ℝ (wordDeriv 2 α u x)
        (convective (wordDeriv 1 (fun _ : Fin 1 => α 0) u)
          (wordDeriv 1 (Fin.tail α) u) x))
    have habs2 := abs_add_le
      (inner ℝ (wordDeriv 2 α u x) (convective (wordDeriv 2 α u) u x))
      (inner ℝ (wordDeriv 2 α u x)
        (convective (wordDeriv 1 (Fin.tail α) u)
          (wordDeriv 1 (fun _ : Fin 1 => α 0) u) x))
    linarith [habs1, habs2]
  have hA : |inner ℝ (wordDeriv 2 α u x) (convective (wordDeriv 2 α u) u x)| ≤
      gradSup u * ‖wordDeriv 2 α u x‖ ^ 2 := by
    have h := abs_inner_convective_le (v := wordDeriv 2 α u) (wvec := wordDeriv 2 α u)
      (f := u) x hd_u
    have : ‖wordDeriv 2 α u x‖ * ‖fderiv ℝ u x‖ * ‖wordDeriv 2 α u x‖ ≤
        gradSup u * ‖wordDeriv 2 α u x‖ ^ 2 := by
      nlinarith [hgs, norm_nonneg (wordDeriv 2 α u x), norm_nonneg (fderiv ℝ u x)]
    exact h.trans this
  have hterm (β γ : Fin 1 → Fin 3)
      (hd : DifferentiableAt ℝ (wordDeriv 1 γ u) x) :
      |inner ℝ (wordDeriv 2 α u x) (convective (wordDeriv 1 β u) (wordDeriv 1 γ u) x)| ≤
        gradSup u *
          (‖wordDeriv 2 α u x‖ ^ 2 +
            3 * ∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i γ) u x‖ ^ 2) := by
    have h := abs_inner_convective_le (v := wordDeriv 2 α u) (wvec := wordDeriv 1 β u)
      (f := wordDeriv 1 γ u) x hd
    have hop := opNorm_fderiv_wordDeriv_one_le hu γ x
    have hω := (norm_wordDeriv_one_le β u x).trans hgs
    have hmul :
        ‖wordDeriv 2 α u x‖ * ‖fderiv ℝ (wordDeriv 1 γ u) x‖ *
          ‖wordDeriv 1 β u x‖ ≤
        (‖wordDeriv 2 α u x‖ *
          ∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i γ) u x‖) * gradSup u := by
      have hnnA : 0 ≤ ‖wordDeriv 2 α u x‖ := norm_nonneg _
      have hnnS : 0 ≤ ∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i γ) u x‖ :=
        Finset.sum_nonneg fun _ _ => norm_nonneg _
      have hnnw : 0 ≤ ‖wordDeriv 1 β u x‖ := norm_nonneg _
      have h1 : ‖wordDeriv 2 α u x‖ * ‖fderiv ℝ (wordDeriv 1 γ u) x‖ ≤
          ‖wordDeriv 2 α u x‖ *
            ∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i γ) u x‖ :=
        mul_le_mul_of_nonneg_left hop hnnA
      exact mul_le_mul h1 hω hnnw (mul_nonneg hnnA hnnS)
    have hamg : ‖wordDeriv 2 α u x‖ *
        ∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i γ) u x‖ ≤
          ‖wordDeriv 2 α u x‖ ^ 2 +
            3 * ∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i γ) u x‖ ^ 2 := by
      have h1 := mul_le_sq_add_sq (‖wordDeriv 2 α u x‖)
        (∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i γ) u x‖)
      have h2 : (∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i γ) u x‖) ^ 2 ≤
          3 * ∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i γ) u x‖ ^ 2 := by
        have := sq_sum_le_card_mul_sum_sq
          (s := (Finset.univ : Finset (Fin 3)))
          (f := fun i : Fin 3 => ‖wordDeriv 2 (Fin.cons i γ) u x‖)
        simpa [Finset.card_univ, Fintype.card_fin] using this
      nlinarith [h1, h2]
    have hscale :
        (‖wordDeriv 2 α u x‖ *
          ∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i γ) u x‖) * gradSup u ≤
          gradSup u *
            (‖wordDeriv 2 α u x‖ ^ 2 +
              3 * ∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i γ) u x‖ ^ 2) :=
      (mul_le_mul_of_nonneg_right hamg hgs0).trans_eq (by ring)
    exact (h.trans hmul).trans hscale
  have hB := hterm (Fin.tail α) (fun _ : Fin 1 => α 0) hd_i
  have hC := hterm (fun _ : Fin 1 => α 0) (Fin.tail α) hd_j
  have : |inner ℝ (wordDeriv 2 α u x) (convectiveCommutator 2 α u x)| ≤
      gradSup u * ‖wordDeriv 2 α u x‖ ^ 2 +
        gradSup u *
          (‖wordDeriv 2 α u x‖ ^ 2 +
            3 * ∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i (fun _ : Fin 1 => α 0)) u x‖ ^ 2) +
        gradSup u *
          (‖wordDeriv 2 α u x‖ ^ 2 +
            3 * ∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i (Fin.tail α)) u x‖ ^ 2) :=
    (hsplit.trans (add_le_add (add_le_add hA hB) hC))
  have hrewrite :
      gradSup u * ‖wordDeriv 2 α u x‖ ^ 2 +
        gradSup u *
          (‖wordDeriv 2 α u x‖ ^ 2 +
            3 * ∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i (fun _ : Fin 1 => α 0)) u x‖ ^ 2) +
        gradSup u *
          (‖wordDeriv 2 α u x‖ ^ 2 +
            3 * ∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i (Fin.tail α)) u x‖ ^ 2) =
      gradSup u *
        (3 * ‖wordDeriv 2 α u x‖ ^ 2 +
          3 * ∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i (fun _ : Fin 1 => α 0)) u x‖ ^ 2 +
          3 * ∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i (Fin.tail α)) u x‖ ^ 2) := by
    ring
  have hloose :
      gradSup u *
          (3 * ‖wordDeriv 2 α u x‖ ^ 2 +
            3 * ∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i (fun _ : Fin 1 => α 0)) u x‖ ^ 2 +
            3 * ∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i (Fin.tail α)) u x‖ ^ 2) ≤
        gradSup u *
          (10 * ‖wordDeriv 2 α u x‖ ^ 2 +
            3 * ∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i (fun _ : Fin 1 => α 0)) u x‖ ^ 2 +
            3 * ∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i (Fin.tail α)) u x‖ ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ hgs0
    nlinarith [sq_nonneg (‖wordDeriv 2 α u x‖)]
  exact this.trans_eq hrewrite |>.trans hloose

lemma integrable_inner_commutator_order_two {u : VelocityField}
    (hu : ContDiff ℝ ∞ u) (hE : sobolevEnergy 3 u < ⊤) (α : Fin 2 → Fin 3) :
    Integrable (fun x =>
      inner ℝ (wordDeriv 2 α u x) (convectiveCommutator 2 α u x)) volume := by
  have hcont : Continuous
      (fun x => inner ℝ (wordDeriv 2 α u x) (convectiveCommutator 2 α u x)) :=
    (contDiff_wordDeriv (k := 2) α hu).continuous.inner
      ((contDiff_wordDeriv (k := 2) α (contDiff_convective hu hu)).continuous.sub
        (contDiff_convective hu (contDiff_wordDeriv (k := 2) α hu)).continuous)
  have hgs0 : 0 ≤ gradSup u :=
    (norm_nonneg (fderiv ℝ u 0)).trans (le_gradSup hu hE 0)
  have hmaj : Integrable (fun x =>
      gradSup u *
        (10 * ‖wordDeriv 2 α u x‖ ^ 2 +
          3 * ∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i (fun _ : Fin 1 => α 0)) u x‖ ^ 2 +
          3 * ∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i (Fin.tail α)) u x‖ ^ 2)) volume := by
    have hα := (integrable_wordDeriv_sq hu hE (by norm_num : (2 : ℕ) ≤ 3) α).const_mul 10
    have hi := integrable_finset_sum (Finset.univ : Finset (Fin 3))
      (fun i _ => integrable_wordDeriv_sq hu hE (by norm_num : (2 : ℕ) ≤ 3)
        (Fin.cons i (fun _ : Fin 1 => α 0)))
    have hj := integrable_finset_sum (Finset.univ : Finset (Fin 3))
      (fun i _ => integrable_wordDeriv_sq hu hE (by norm_num : (2 : ℕ) ≤ 3)
        (Fin.cons i (Fin.tail α)))
    exact (hα.add (hi.const_mul 3)).add (hj.const_mul 3) |>.const_mul (gradSup u)
  exact hmaj.mono' hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using abs_pairing_commutator_order_two_le hu hE α x)

/-- Absolute pairing of the second-order commutator is at most
`28 * gradSup u * hsSq 3 u`. -/
theorem abs_integral_commutator_order_two {u : VelocityField}
    (hu : ContDiff ℝ ∞ u) (hE : sobolevEnergy 3 u < ⊤) (α : Fin 2 → Fin 3) :
    |∫ x, inner ℝ (wordDeriv 2 α u x) (convectiveCommutator 2 α u x) ∂volume| ≤
      28 * gradSup u * hsSq 3 u := by
  have hinter := integrable_inner_commutator_order_two hu hE α
  have habs :
      |∫ x, inner ℝ (wordDeriv 2 α u x) (convectiveCommutator 2 α u x) ∂volume| ≤
        ∫ x, |inner ℝ (wordDeriv 2 α u x) (convectiveCommutator 2 α u x)| ∂volume := by
    simpa [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm
        (f := fun x => inner ℝ (wordDeriv 2 α u x) (convectiveCommutator 2 α u x)))
  have hgs0 : 0 ≤ gradSup u :=
    (norm_nonneg (fderiv ℝ u 0)).trans (le_gradSup hu hE 0)
  have hpt := fun x => abs_pairing_commutator_order_two_le hu hE α x
  have hmaj : Integrable (fun x =>
      gradSup u *
        (10 * ‖wordDeriv 2 α u x‖ ^ 2 +
          3 * ∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i (fun _ : Fin 1 => α 0)) u x‖ ^ 2 +
          3 * ∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i (Fin.tail α)) u x‖ ^ 2)) volume := by
    have hα := (integrable_wordDeriv_sq hu hE (by norm_num : (2 : ℕ) ≤ 3) α).const_mul 10
    have hi := integrable_finset_sum (Finset.univ : Finset (Fin 3))
      (fun i _ => integrable_wordDeriv_sq hu hE (by norm_num : (2 : ℕ) ≤ 3)
        (Fin.cons i (fun _ : Fin 1 => α 0)))
    have hj := integrable_finset_sum (Finset.univ : Finset (Fin 3))
      (fun i _ => integrable_wordDeriv_sq hu hE (by norm_num : (2 : ℕ) ≤ 3)
        (Fin.cons i (Fin.tail α)))
    exact (hα.add (hi.const_mul 3)).add (hj.const_mul 3) |>.const_mul (gradSup u)
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun _ => abs_nonneg _) hmaj
    (Filter.Eventually.of_forall hpt)
  have hαint := integrable_wordDeriv_sq hu hE (by norm_num : (2 : ℕ) ≤ 3) α
  have hi := integrable_finset_sum (Finset.univ : Finset (Fin 3))
    (fun i _ => integrable_wordDeriv_sq hu hE (by norm_num : (2 : ℕ) ≤ 3)
      (Fin.cons i (fun _ : Fin 1 => α 0)))
  have hj := integrable_finset_sum (Finset.univ : Finset (Fin 3))
    (fun i _ => integrable_wordDeriv_sq hu hE (by norm_num : (2 : ℕ) ≤ 3)
      (Fin.cons i (Fin.tail α)))
  have hrhs :
      ∫ x, gradSup u *
          (10 * ‖wordDeriv 2 α u x‖ ^ 2 +
            3 * ∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i (fun _ : Fin 1 => α 0)) u x‖ ^ 2 +
            3 * ∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i (Fin.tail α)) u x‖ ^ 2) ∂volume =
        gradSup u *
          (10 * ∫ x, ‖wordDeriv 2 α u x‖ ^ 2 ∂volume +
            3 * ∑ i : Fin 3,
              ∫ x, ‖wordDeriv 2 (Fin.cons i (fun _ : Fin 1 => α 0)) u x‖ ^ 2 ∂volume +
            3 * ∑ i : Fin 3,
              ∫ x, ‖wordDeriv 2 (Fin.cons i (Fin.tail α)) u x‖ ^ 2 ∂volume) := by
    have hsumi := integral_finset_sum (Finset.univ : Finset (Fin 3))
      (fun i _ => integrable_wordDeriv_sq hu hE (by norm_num : (2 : ℕ) ≤ 3)
        (Fin.cons i (fun _ : Fin 1 => α 0)))
    have hsumj := integral_finset_sum (Finset.univ : Finset (Fin 3))
      (fun i _ => integrable_wordDeriv_sq hu hE (by norm_num : (2 : ℕ) ≤ 3)
        (Fin.cons i (Fin.tail α)))
    rw [integral_const_mul]
    congr 1
    let f : T3 → ℝ := fun x => 10 * ‖wordDeriv 2 α u x‖ ^ 2
    let g : T3 → ℝ := fun x =>
      3 * ∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i (fun _ : Fin 1 => α 0)) u x‖ ^ 2
    let h : T3 → ℝ := fun x =>
      3 * ∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i (Fin.tail α)) u x‖ ^ 2
    have hfun : (fun x =>
        10 * ‖wordDeriv 2 α u x‖ ^ 2 +
          3 * ∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i (fun _ : Fin 1 => α 0)) u x‖ ^ 2 +
          3 * ∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i (Fin.tail α)) u x‖ ^ 2) =
        f + g + h := by
      ext x
      simp [f, g, h, Pi.add_apply]
    have hf : Integrable f volume := hαint.const_mul 10
    have hg : Integrable g volume := hi.const_mul 3
    have hh : Integrable h volume := hj.const_mul 3
    rw [hfun]
    calc
      integral volume (f + g + h)
          = ∫ x, (f + g) x + h x ∂volume := rfl
      _ = ∫ x, (f + g) x ∂volume + ∫ x, h x ∂volume :=
          integral_add (hf.add hg) hh
      _ = ∫ x, f x + g x ∂volume + ∫ x, h x ∂volume := rfl
      _ = ∫ x, f x ∂volume + ∫ x, g x ∂volume + ∫ x, h x ∂volume := by
          rw [integral_add hf hg]
      _ = 10 * ∫ x, ‖wordDeriv 2 α u x‖ ^ 2 ∂volume +
            3 * ∫ x, ∑ i : Fin 3,
              ‖wordDeriv 2 (Fin.cons i (fun _ : Fin 1 => α 0)) u x‖ ^ 2 ∂volume +
            3 * ∫ x, ∑ i : Fin 3,
              ‖wordDeriv 2 (Fin.cons i (Fin.tail α)) u x‖ ^ 2 ∂volume := by
          simp only [f, g, h, integral_const_mul]
      _ = 10 * ∫ x, ‖wordDeriv 2 α u x‖ ^ 2 ∂volume +
            3 * ∑ i : Fin 3,
              ∫ x, ‖wordDeriv 2 (Fin.cons i (fun _ : Fin 1 => α 0)) u x‖ ^ 2 ∂volume +
            3 * ∑ i : Fin 3,
              ∫ x, ‖wordDeriv 2 (Fin.cons i (Fin.tail α)) u x‖ ^ 2 ∂volume := by
          rw [hsumi, hsumj]
  have hbound :
      gradSup u *
          (10 * ∫ x, ‖wordDeriv 2 α u x‖ ^ 2 ∂volume +
            3 * ∑ i : Fin 3,
              ∫ x, ‖wordDeriv 2 (Fin.cons i (fun _ : Fin 1 => α 0)) u x‖ ^ 2 ∂volume +
            3 * ∑ i : Fin 3,
              ∫ x, ‖wordDeriv 2 (Fin.cons i (Fin.tail α)) u x‖ ^ 2 ∂volume) ≤
        28 * gradSup u * hsSq 3 u := by
    have h1 := integral_wordDeriv_sq_le hu hE (by norm_num : (2 : ℕ) ≤ 3) α
    have h2 : ∑ i : Fin 3,
        ∫ x, ‖wordDeriv 2 (Fin.cons i (fun _ : Fin 1 => α 0)) u x‖ ^ 2 ∂volume ≤
          3 * hsSq 3 u := by
      have : ∀ i : Fin 3,
          ∫ x, ‖wordDeriv 2 (Fin.cons i (fun _ : Fin 1 => α 0)) u x‖ ^ 2 ∂volume ≤
            hsSq 3 u := fun i =>
        integral_wordDeriv_sq_le hu hE (by norm_num : (2 : ℕ) ≤ 3)
          (Fin.cons i (fun _ : Fin 1 => α 0))
      have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3)))
        (fun i _ => this i)
      have hcard : ∑ _i : Fin 3, hsSq 3 u = 3 * hsSq 3 u := by
        simp [Finset.sum_const, Fintype.card_fin]
      exact hsum.trans_eq hcard
    have h3 : ∑ i : Fin 3,
        ∫ x, ‖wordDeriv 2 (Fin.cons i (Fin.tail α)) u x‖ ^ 2 ∂volume ≤
          3 * hsSq 3 u := by
      have : ∀ i : Fin 3,
          ∫ x, ‖wordDeriv 2 (Fin.cons i (Fin.tail α)) u x‖ ^ 2 ∂volume ≤
            hsSq 3 u := fun i =>
        integral_wordDeriv_sq_le hu hE (by norm_num : (2 : ℕ) ≤ 3)
          (Fin.cons i (Fin.tail α))
      have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3)))
        (fun i _ => this i)
      have hcard : ∑ _i : Fin 3, hsSq 3 u = 3 * hsSq 3 u := by
        simp [Finset.sum_const, Fintype.card_fin]
      exact hsum.trans_eq hcard
    have hE0 : 0 ≤ hsSq 3 u := ENNReal.toReal_nonneg
    have : 10 * ∫ x, ‖wordDeriv 2 α u x‖ ^ 2 ∂volume +
        3 * ∑ i : Fin 3,
          ∫ x, ‖wordDeriv 2 (Fin.cons i (fun _ : Fin 1 => α 0)) u x‖ ^ 2 ∂volume +
        3 * ∑ i : Fin 3,
          ∫ x, ‖wordDeriv 2 (Fin.cons i (Fin.tail α)) u x‖ ^ 2 ∂volume ≤
        28 * hsSq 3 u := by
      nlinarith [h1, h2, h3, hE0]
    calc
      _ ≤ gradSup u * (28 * hsSq 3 u) := mul_le_mul_of_nonneg_left this hgs0
      _ = 28 * gradSup u * hsSq 3 u := by ring
  exact habs.trans (hmono.trans_eq hrhs |>.trans hbound)

/-- `∂_{α 0}` of a length-`k` word is the length-`(k+1)` word. -/
lemma wordDeriv_outer {k : ℕ} (α : Fin (k + 1) → Fin 3) {f : VelocityField}
    (hf : ContDiff ℝ ∞ f) :
    wordDeriv 1 (fun _ : Fin 1 => α 0) (wordDeriv k (Fin.tail α) f) =
      wordDeriv (k + 1) α f := by
  funext y
  simpa [wordDeriv_one] using
    (congrFun (wordDeriv_succ (k := k) α (f := f) hf) y).symm

/-- Prepending an index `i` is `∂_i` of the shorter word. -/
lemma wordDeriv_cons_fun {k : ℕ} (i : Fin 3) (α : Fin k → Fin 3)
    {f : VelocityField} (hf : ContDiff ℝ ∞ f) :
    wordDeriv 1 (fun _ : Fin 1 => i) (wordDeriv k α f) =
      wordDeriv (k + 1) (Fin.cons i α) f := by
  funext y
  simpa [wordDeriv_one, Fin.tail_cons] using
    (congrFun (wordDeriv_succ (k := k) (Fin.cons i α) (f := f) hf) y).symm

/-- Eight-term Leibniz expansion of `∂^α((u·∇)v)` at order three. -/
lemma wordDeriv_convective_order_three {u v : VelocityField}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (α : Fin 3 → Fin 3) (x : T3) :
    wordDeriv 3 α (convective u v) x =
      convective (wordDeriv 3 α u) v x
        + convective (wordDeriv 2 (Fin.tail α) u)
            (wordDeriv 1 (fun _ : Fin 1 => α 0) v) x
        + convective
            (wordDeriv 2 (Fin.cons (α 0) (Fin.tail (Fin.tail α))) u)
            (wordDeriv 1 (fun _ : Fin 1 => (Fin.tail α) 0) v) x
        + convective (wordDeriv 1 (Fin.tail (Fin.tail α)) u)
            (wordDeriv 2 (Fin.cons (α 0) (fun _ : Fin 1 => (Fin.tail α) 0)) v) x
        + convective
            (wordDeriv 2 (Fin.cons (α 0) (fun _ : Fin 1 => (Fin.tail α) 0)) u)
            (wordDeriv 1 (Fin.tail (Fin.tail α)) v) x
        + convective (wordDeriv 1 (fun _ : Fin 1 => (Fin.tail α) 0) u)
            (wordDeriv 2 (Fin.cons (α 0) (Fin.tail (Fin.tail α))) v) x
        + convective (wordDeriv 1 (fun _ : Fin 1 => α 0) u)
            (wordDeriv 2 (Fin.tail α) v) x
        + convective u (wordDeriv 3 α v) x := by
  have hconv : ContDiff ℝ ∞ (convective u v) := contDiff_convective hu hv
  set A : VelocityField := convective (wordDeriv 2 (Fin.tail α) u) v
  set B : VelocityField :=
    convective (wordDeriv 1 (Fin.tail (Fin.tail α)) u)
      (wordDeriv 1 (fun _ : Fin 1 => (Fin.tail α) 0) v)
  set C : VelocityField :=
    convective (wordDeriv 1 (fun _ : Fin 1 => (Fin.tail α) 0) u)
      (wordDeriv 1 (Fin.tail (Fin.tail α)) v)
  set D : VelocityField := convective u (wordDeriv 2 (Fin.tail α) v)
  have hfun : wordDeriv 2 (Fin.tail α) (convective u v) = A + B + C + D := by
    funext y
    simpa [A, B, C, D, Pi.add_apply] using
      wordDeriv_convective_order_two hu hv (Fin.tail α) y
  have hA : ContDiff ℝ ∞ A :=
    contDiff_convective (contDiff_wordDeriv (k := 2) (Fin.tail α) hu) hv
  have hB : ContDiff ℝ ∞ B :=
    contDiff_convective (contDiff_wordDeriv (k := 1) (Fin.tail (Fin.tail α)) hu)
      (contDiff_wordDeriv (k := 1) (fun _ : Fin 1 => (Fin.tail α) 0) hv)
  have hC : ContDiff ℝ ∞ C :=
    contDiff_convective
      (contDiff_wordDeriv (k := 1) (fun _ : Fin 1 => (Fin.tail α) 0) hu)
      (contDiff_wordDeriv (k := 1) (Fin.tail (Fin.tail α)) hv)
  have hD : ContDiff ℝ ∞ D :=
    contDiff_convective hu (contDiff_wordDeriv (k := 2) (Fin.tail α) hv)
  have hAB : ContDiff ℝ ∞ (A + B) := hA.add hB
  have hABC : ContDiff ℝ ∞ (A + B + C) := hAB.add hC
  set i0 : Fin 1 → Fin 3 := fun _ => α 0
  have hadd :
      wordDeriv 3 α (convective u v) x =
        wordDeriv 1 i0 A x + wordDeriv 1 i0 B x +
          wordDeriv 1 i0 C x + wordDeriv 1 i0 D x := by
    have houter : wordDeriv 3 α (convective u v) x =
        wordDeriv 1 i0 (wordDeriv 2 (Fin.tail α) (convective u v)) x := by
      simpa [i0] using
        (congrFun (wordDeriv_outer (k := 2) α hconv) x).symm
    rw [houter, hfun]
    have hsum := congrFun
      (wordDeriv_add (k := 1) i0 (contDiff_of_infty hABC) (contDiff_of_infty hD)) x
    have hsum2 := congrFun
      (wordDeriv_add (k := 1) i0 (contDiff_of_infty hAB) (contDiff_of_infty hC)) x
    have hsum3 := congrFun
      (wordDeriv_add (k := 1) i0 (contDiff_of_infty hA) (contDiff_of_infty hB)) x
    simp only [hsum, hsum2, hsum3, Pi.add_apply]
  have h1 := convective_leibniz_one
    (contDiff_wordDeriv (k := 2) (Fin.tail α) hu) hv i0 x
  have h2 := convective_leibniz_one
    (contDiff_wordDeriv (k := 1) (Fin.tail (Fin.tail α)) hu)
    (contDiff_wordDeriv (k := 1) (fun _ : Fin 1 => (Fin.tail α) 0) hv) i0 x
  have h3 := convective_leibniz_one
    (contDiff_wordDeriv (k := 1) (fun _ : Fin 1 => (Fin.tail α) 0) hu)
    (contDiff_wordDeriv (k := 1) (Fin.tail (Fin.tail α)) hv) i0 x
  have h4 := convective_leibniz_one hu
    (contDiff_wordDeriv (k := 2) (Fin.tail α) hv) i0 x
  have hid3u := wordDeriv_outer (k := 2) α hu
  have hid3v := wordDeriv_outer (k := 2) α hv
  have hid2u_in := wordDeriv_cons_fun (α 0) (Fin.tail (Fin.tail α)) hu
  have hid2v_in := wordDeriv_cons_fun (α 0) (Fin.tail (Fin.tail α)) hv
  have hid2u_mid := wordDeriv_cons_fun (α 0) (fun _ : Fin 1 => (Fin.tail α) 0) hu
  have hid2v_mid := wordDeriv_cons_fun (α 0) (fun _ : Fin 1 => (Fin.tail α) 0) hv
  simp only [i0] at hadd h1 h2 h3 h4
  rw [hadd, h1, h2, h3, h4, hid3u, hid3v, hid2u_in, hid2v_in, hid2u_mid,
    hid2v_mid]
  abel

/-- `[∂^α, u·∇]u` at order three is the eight-term expansion minus `(u·∇)(∂^α u)`. -/
lemma convectiveCommutator_order_three {u : VelocityField} (hu : ContDiff ℝ ∞ u)
    (α : Fin 3 → Fin 3) (x : T3) :
    convectiveCommutator 3 α u x =
      convective (wordDeriv 3 α u) u x
        + convective (wordDeriv 2 (Fin.tail α) u)
            (wordDeriv 1 (fun _ : Fin 1 => α 0) u) x
        + convective
            (wordDeriv 2 (Fin.cons (α 0) (Fin.tail (Fin.tail α))) u)
            (wordDeriv 1 (fun _ : Fin 1 => (Fin.tail α) 0) u) x
        + convective (wordDeriv 1 (Fin.tail (Fin.tail α)) u)
            (wordDeriv 2 (Fin.cons (α 0) (fun _ : Fin 1 => (Fin.tail α) 0)) u) x
        + convective
            (wordDeriv 2 (Fin.cons (α 0) (fun _ : Fin 1 => (Fin.tail α) 0)) u)
            (wordDeriv 1 (Fin.tail (Fin.tail α)) u) x
        + convective (wordDeriv 1 (fun _ : Fin 1 => (Fin.tail α) 0) u)
            (wordDeriv 2 (Fin.cons (α 0) (Fin.tail (Fin.tail α))) u) x
        + convective (wordDeriv 1 (fun _ : Fin 1 => α 0) u)
            (wordDeriv 2 (Fin.tail α) u) x := by
  have h := wordDeriv_convective_order_three hu hu α x
  simp only [convectiveCommutator, h]
  abel

lemma integrable_wordDeriv_two_pow_four {u : VelocityField}
    (hu : ContDiff ℝ ∞ u) (hE : sobolevEnergy 3 u < ⊤) (α : Fin 2 → Fin 3) :
    Integrable (fun x => ‖wordDeriv 2 α u x‖ ^ (4 : ℕ)) volume := by
  obtain ⟨K1, hK1nn, hK1b⟩ := exists_bound_unitBump_fderiv
  obtain ⟨K2, hK2nn, hK2b⟩ := exists_bound_unitBump_partiali2
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

lemma integral_wordDeriv_two_pow_four_le {u : VelocityField}
    (hu : ContDiff ℝ ∞ u) (hE : sobolevEnergy 3 u < ⊤) (α : Fin 2 → Fin 3)
    {C : ℝ} (hC : 0 ≤ C)
    (hgn : (∑ (β : Fin 2 → Fin 3),
        ∫ x, ‖wordDeriv 2 β u x‖ ^ (4 : ℕ) ∂volume) ≤
      C * gradSup u ^ 2 * hsSq 3 u) :
    ∫ x, ‖wordDeriv 2 α u x‖ ^ (4 : ℕ) ∂volume ≤
      C * gradSup u ^ 2 * hsSq 3 u := by
  have hint : ∀ β : Fin 2 → Fin 3,
      Integrable (fun x => ‖wordDeriv 2 β u x‖ ^ (4 : ℕ)) volume :=
    fun β => integrable_wordDeriv_two_pow_four hu hE β
  have hnn : ∀ β : Fin 2 → Fin 3,
      0 ≤ ∫ x, ‖wordDeriv 2 β u x‖ ^ (4 : ℕ) ∂volume := fun β =>
    integral_nonneg fun _ => pow_nonneg (norm_nonneg _) _
  have hsingle := Finset.single_le_sum (s := (Finset.univ : Finset (Fin 2 → Fin 3)))
    (fun β _ => hnn β) (Finset.mem_univ α)
  exact hsingle.trans hgn

lemma integrable_mul_of_sq {f g : T3 → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfc : Continuous f) (hgc : Continuous g)
    (hfi : Integrable (fun x => f x ^ 2) volume)
    (hgi : Integrable (fun x => g x ^ 2) volume) :
    Integrable (fun x => f x * g x) volume := by
  refine ((hfi.add hgi).const_mul (1 / 2)).mono'
    (hfc.mul hgc).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have hprod : 0 ≤ f x * g x := mul_nonneg (hf0 x) (hg0 x)
  have ham : f x * g x ≤ (f x ^ 2 + g x ^ 2) / 2 := by
    nlinarith [sq_nonneg (f x - g x)]
  have habs : |f x| * |g x| = f x * g x := by
    rw [abs_of_nonneg (hf0 x), abs_of_nonneg (hg0 x)]
  simpa [Real.norm_eq_abs, habs, div_eq_inv_mul] using ham

lemma integral_nonneg_mul_le_sqrt {f g : T3 → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfc : Continuous f) (hgc : Continuous g)
    (hfi : Integrable (fun x => f x ^ 2) volume)
    (hgi : Integrable (fun x => g x ^ 2) volume) :
    ∫ x, f x * g x ∂volume ≤
      Real.sqrt (∫ x, f x ^ 2 ∂volume) *
        Real.sqrt (∫ x, g x ^ 2 ∂volume) := by
  have hf2 : MemLp f 2 volume :=
    (memLp_two_iff_integrable_sq hfc.aestronglyMeasurable).2 hfi
  have hg2 : MemLp g 2 volume :=
    (memLp_two_iff_integrable_sq hgc.aestronglyMeasurable).2 hgi
  have hf2' : MemLp f (ENNReal.ofReal 2) volume := by convert hf2; norm_num
  have hg2' : MemLp g (ENNReal.ofReal 2) volume := by convert hg2; norm_num
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hg0) hf2' hg2'
  have hfpow : (fun x => f x ^ (2 : ℝ)) = fun x => f x ^ 2 := by
    funext x; exact Real.rpow_natCast (f x) 2
  have hgpow : (fun x => g x ^ (2 : ℝ)) = fun x => g x ^ 2 := by
    funext x; exact Real.rpow_natCast (g x) 2
  have hsqrt : ∀ {a : ℝ}, (0 ≤ a) → a ^ (1 / 2 : ℝ) = Real.sqrt a := fun {a} ha =>
    (Real.sqrt_eq_rpow a).symm
  have hf2nn : 0 ≤ ∫ x, f x ^ 2 ∂volume := integral_nonneg fun x => sq_nonneg (f x)
  have hg2nn : 0 ≤ ∫ x, g x ^ 2 ∂volume := integral_nonneg fun x => sq_nonneg (g x)
  simp only [hfpow, hgpow] at h
  have hfroot : (∫ x, f x ^ 2 ∂volume) ^ (2⁻¹ : ℝ) =
      Real.sqrt (∫ x, f x ^ 2 ∂volume) := by
    simp only [inv_eq_one_div]
    exact (Real.sqrt_eq_rpow _).symm
  have hgroot : (∫ x, g x ^ 2 ∂volume) ^ (2⁻¹ : ℝ) =
      Real.sqrt (∫ x, g x ^ 2 ∂volume) := by
    simp only [inv_eq_one_div]
    exact (Real.sqrt_eq_rpow _).symm
  simpa [hfroot, hgroot] using h

lemma integrable_norm_mul_mul {f g h : T3 → T3}
    (hfc : Continuous f) (hgc : Continuous g) (hhc : Continuous h)
    (hf2 : Integrable (fun x => ‖f x‖ ^ 2) volume)
    (hg4 : Integrable (fun x => ‖g x‖ ^ (4 : ℕ)) volume)
    (hh4 : Integrable (fun x => ‖h x‖ ^ (4 : ℕ)) volume) :
    Integrable (fun x => ‖f x‖ * ‖g x‖ * ‖h x‖) volume := by
  refine ((hf2.const_mul (1 / 2)).add (hg4.const_mul (1 / 4)) |>.add
      (hh4.const_mul (1 / 4))).mono'
    (((hfc.norm.mul hgc.norm).mul hhc.norm).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  have hnn : 0 ≤ ‖f x‖ * ‖g x‖ * ‖h x‖ :=
    mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  have ham := mul_mul_le_sq_add_pow_four (‖f x‖) (‖g x‖) (‖h x‖)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  simpa [Real.norm_eq_abs, abs_of_nonneg hnn, div_eq_inv_mul] using ham

lemma integral_norm_mul_mul_le_L2_L4_L4 {f g h : T3 → T3}
    (hfc : Continuous f) (hgc : Continuous g) (hhc : Continuous h)
    (hf2 : Integrable (fun x => ‖f x‖ ^ 2) volume)
    (hg4 : Integrable (fun x => ‖g x‖ ^ (4 : ℕ)) volume)
    (hh4 : Integrable (fun x => ‖h x‖ ^ (4 : ℕ)) volume) :
    ∫ x, ‖f x‖ * ‖g x‖ * ‖h x‖ ∂volume ≤
      Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂volume) *
        Real.sqrt (Real.sqrt (∫ x, ‖g x‖ ^ (4 : ℕ) ∂volume) *
          Real.sqrt (∫ x, ‖h x‖ ^ (4 : ℕ) ∂volume)) := by
  have h1 := integral_nonneg_mul_le_sqrt
    (fun x => norm_nonneg (f x))
    (fun x => mul_nonneg (norm_nonneg (g x)) (norm_nonneg (h x)))
    hfc.norm (hgc.norm.mul hhc.norm) hf2
    (by
      have hg2 : Integrable (fun x => (‖g x‖ ^ 2) ^ 2) volume := by
        convert hg4 using 1
        funext x; ring
      have hh2 : Integrable (fun x => (‖h x‖ ^ 2) ^ 2) volume := by
        convert hh4 using 1
        funext x; ring
      have heq : (fun x => (‖g x‖ * ‖h x‖) ^ 2) =
          fun x => ‖g x‖ ^ 2 * ‖h x‖ ^ 2 := by
        funext x; ring
      rw [heq]
      exact integrable_mul_of_sq (fun x => sq_nonneg _) (fun x => sq_nonneg _)
        (hgc.norm.pow 2) (hhc.norm.pow 2) hg2 hh2)
  have h2 := integral_nonneg_mul_le_sqrt
    (fun x => sq_nonneg (‖g x‖)) (fun x => sq_nonneg (‖h x‖))
    (hgc.norm.pow 2) (hhc.norm.pow 2)
    (by convert hg4 using 1; funext x; ring)
    (by convert hh4 using 1; funext x; ring)
  have hrew : (fun x => ‖f x‖ * (‖g x‖ * ‖h x‖)) =
      fun x => ‖f x‖ * ‖g x‖ * ‖h x‖ := by
    funext x; ac_rfl
  have hsqg : (fun x => (‖g x‖ ^ 2) ^ 2) = fun x => ‖g x‖ ^ (4 : ℕ) := by
    funext x; ring
  have hsqh : (fun x => (‖h x‖ ^ 2) ^ 2) = fun x => ‖h x‖ ^ (4 : ℕ) := by
    funext x; ring
  -- ∫ ‖f‖(‖g‖‖h‖) ≤ sqrt(∫‖f‖²) * sqrt(∫ ‖g‖²‖h‖²)
  -- and ∫ ‖g‖²‖h‖² ≤ sqrt(∫‖g‖⁴) * sqrt(∫‖h‖⁴)
  have : ∫ x, ‖f x‖ * ‖g x‖ * ‖h x‖ ∂volume ≤
      Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂volume) *
        Real.sqrt (∫ x, ‖g x‖ ^ 2 * ‖h x‖ ^ 2 ∂volume) := by
    simpa [hrew, mul_pow] using h1
  refine this.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  have hnn : 0 ≤ ∫ x, ‖g x‖ ^ 2 * ‖h x‖ ^ 2 ∂volume :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have h2' : ∫ x, ‖g x‖ ^ 2 * ‖h x‖ ^ 2 ∂volume ≤
      Real.sqrt (∫ x, ‖g x‖ ^ (4 : ℕ) ∂volume) *
        Real.sqrt (∫ x, ‖h x‖ ^ (4 : ℕ) ∂volume) := by
    simpa [hsqg, hsqh] using h2
  exact Real.sqrt_le_sqrt h2'

lemma rpow_quarter_prod_le {a b B : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hB : 0 ≤ B) (haB : a ≤ B) (hbB : b ≤ B) :
    Real.sqrt (Real.sqrt a * Real.sqrt b) ≤ Real.sqrt B := by
  have hsa : 0 ≤ Real.sqrt a := Real.sqrt_nonneg _
  have hsb : 0 ≤ Real.sqrt b := Real.sqrt_nonneg _
  have hab : Real.sqrt a * Real.sqrt b ≤ Real.sqrt B * Real.sqrt B :=
    mul_le_mul (Real.sqrt_le_sqrt haB) (Real.sqrt_le_sqrt hbB) hsb (Real.sqrt_nonneg _)
  have : Real.sqrt B * Real.sqrt B = B := Real.mul_self_sqrt hB
  exact Real.sqrt_le_sqrt (hab.trans_eq this)

lemma sqrt_mul_energy_le (C g E : ℝ) (hC : 0 ≤ C) (hg : 0 ≤ g) (hE : 0 ≤ E) :
    Real.sqrt E * Real.sqrt (C * g ^ 2 * E) ≤ (C + 1) * g * E := by
  have hB : 0 ≤ C * g ^ 2 * E := mul_nonneg (mul_nonneg hC (sq_nonneg _)) hE
  have h1 : Real.sqrt (C * g ^ 2 * E) = Real.sqrt C * g * Real.sqrt E := by
    have h2 : Real.sqrt (C * (g ^ 2 * E)) = Real.sqrt C * Real.sqrt (g ^ 2 * E) :=
      Real.sqrt_mul hC (g ^ 2 * E)
    have h3 : Real.sqrt (g ^ 2 * E) = g * Real.sqrt E := by
      have := Real.sqrt_mul (sq_nonneg g) E
      simpa [Real.sqrt_sq hg] using this
    calc
      Real.sqrt (C * g ^ 2 * E) = Real.sqrt (C * (g ^ 2 * E)) := by ring_nf
      _ = Real.sqrt C * Real.sqrt (g ^ 2 * E) := h2
      _ = Real.sqrt C * (g * Real.sqrt E) := by rw [h3]
      _ = Real.sqrt C * g * Real.sqrt E := by ring
  have hCS : Real.sqrt C ≤ C + 1 := by
    nlinarith [sq_nonneg (Real.sqrt C - 1), Real.sq_sqrt hC]
  have : Real.sqrt E * (Real.sqrt C * g * Real.sqrt E) ≤ (C + 1) * g * E := by
    have hsq : Real.sqrt E * Real.sqrt E = E := Real.mul_self_sqrt hE
    calc
      Real.sqrt E * (Real.sqrt C * g * Real.sqrt E)
          = (Real.sqrt E * Real.sqrt E) * (Real.sqrt C * g) := by ring
      _ = E * (Real.sqrt C * g) := by rw [hsq]
      _ = Real.sqrt C * g * E := by ring
      _ ≤ (C + 1) * g * E :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCS hg) hE
  calc
    Real.sqrt E * Real.sqrt (C * g ^ 2 * E)
        = Real.sqrt E * (Real.sqrt C * g * Real.sqrt E) := by rw [h1]
    _ ≤ (C + 1) * g * E := this


lemma abs_add_seven (a b c d e f g : ℝ) :
    |a + b + c + d + e + f + g| ≤
      |a| + |b| + |c| + |d| + |e| + |f| + |g| := by
  have h1 := abs_add_le (a + b + c + d + e + f) g
  have h2 := abs_add_le (a + b + c + d + e) f
  have h3 := abs_add_le (a + b + c + d) e
  have h4 := abs_add_le (a + b + c) d
  have h5 := abs_add_le (a + b) c
  have h6 := abs_add_le a b
  linarith

lemma integral_abs_inner_convective_three_zero_le {u : VelocityField}
    (hu : ContDiff ℝ ∞ u) (hE : sobolevEnergy 3 u < ⊤) (α : Fin 3 → Fin 3) :
    |∫ x, inner ℝ (wordDeriv 3 α u x)
        (convective (wordDeriv 3 α u) u x) ∂volume| ≤
      gradSup u * hsSq 3 u := by
  have hd : Differentiable ℝ u := (hu.differentiable (by simp))
  have hsq := integrable_wordDeriv_sq hu hE (by norm_num : (3 : ℕ) ≤ 3) α
  have hgs0 : 0 ≤ gradSup u :=
    (norm_nonneg (fderiv ℝ u 0)).trans (le_gradSup hu hE 0)
  have hpt : ∀ x,
      |inner ℝ (wordDeriv 3 α u x) (convective (wordDeriv 3 α u) u x)| ≤
        gradSup u * ‖wordDeriv 3 α u x‖ ^ 2 := by
    intro x
    have h := abs_inner_convective_le (v := wordDeriv 3 α u)
      (wvec := wordDeriv 3 α u) (f := u) x (hd x)
    have hgs := le_gradSup hu hE x
    nlinarith [hgs, norm_nonneg (wordDeriv 3 α u x),
      norm_nonneg (fderiv ℝ u x)]
  have hinter : Integrable
      (fun x => inner ℝ (wordDeriv 3 α u x)
        (convective (wordDeriv 3 α u) u x)) volume := by
    refine (hsq.const_mul (gradSup u)).mono' ?_
      (Filter.Eventually.of_forall fun x => ?_)
    · exact ((contDiff_wordDeriv (k := 3) α hu).continuous.inner
        (contDiff_convective (contDiff_wordDeriv (k := 3) α hu) hu).continuous).aestronglyMeasurable
    · simpa [Real.norm_eq_abs] using hpt x
  have habs :
      |∫ x, inner ℝ (wordDeriv 3 α u x)
          (convective (wordDeriv 3 α u) u x) ∂volume| ≤
        ∫ x, |inner ℝ (wordDeriv 3 α u x)
          (convective (wordDeriv 3 α u) u x)| ∂volume := by
    simpa [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm
        (f := fun x => inner ℝ (wordDeriv 3 α u x)
          (convective (wordDeriv 3 α u) u x)))
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun _ => abs_nonneg _)
    (hsq.const_mul (gradSup u)) (Filter.Eventually.of_forall hpt)
  have hfactor :
      ∫ x, gradSup u * ‖wordDeriv 3 α u x‖ ^ 2 ∂volume =
        gradSup u * ∫ x, ‖wordDeriv 3 α u x‖ ^ 2 ∂volume :=
    integral_const_mul _ _
  have hsqle := integral_wordDeriv_sq_le hu hE (by norm_num : (3 : ℕ) ≤ 3) α
  have : gradSup u * ∫ x, ‖wordDeriv 3 α u x‖ ^ 2 ∂volume ≤
      gradSup u * hsSq 3 u :=
    mul_le_mul_of_nonneg_left hsqle hgs0
  exact habs.trans (hmono.trans_eq hfactor |>.trans this)

lemma integral_abs_inner_convective_one_two_le {u : VelocityField}
    (hu : ContDiff ℝ ∞ u) (hE : sobolevEnergy 3 u < ⊤)
    (α : Fin 3 → Fin 3) (β : Fin 1 → Fin 3) (γ : Fin 2 → Fin 3) :
    |∫ x, inner ℝ (wordDeriv 3 α u x)
        (convective (wordDeriv 1 β u) (wordDeriv 2 γ u) x) ∂volume| ≤
      10 * gradSup u * hsSq 3 u := by
  have hd : Differentiable ℝ (wordDeriv 2 γ u) :=
    (contDiff_wordDeriv (k := 2) γ hu).differentiable (by simp)
  have hsqα := integrable_wordDeriv_sq hu hE (by norm_num : (3 : ℕ) ≤ 3) α
  have hsqi : ∀ i : Fin 3,
      Integrable (fun x => ‖wordDeriv 3 (Fin.cons i γ) u x‖ ^ 2) volume :=
    fun i => integrable_wordDeriv_sq hu hE (by norm_num : (3 : ℕ) ≤ 3)
      (Fin.cons i γ)
  have hgs0 : 0 ≤ gradSup u :=
    (norm_nonneg (fderiv ℝ u 0)).trans (le_gradSup hu hE 0)
  have hpt : ∀ x,
      |inner ℝ (wordDeriv 3 α u x)
        (convective (wordDeriv 1 β u) (wordDeriv 2 γ u) x)| ≤
        gradSup u *
          (‖wordDeriv 3 α u x‖ ^ 2 +
            3 * ∑ i : Fin 3, ‖wordDeriv 3 (Fin.cons i γ) u x‖ ^ 2) := by
    intro x
    have h := abs_inner_convective_le (v := wordDeriv 3 α u)
      (wvec := wordDeriv 1 β u) (f := wordDeriv 2 γ u) x (hd x)
    have hop := opNorm_fderiv_wordDeriv_two_le hu γ x
    have hω := (norm_wordDeriv_one_le β u x).trans (le_gradSup hu hE x)
    have hnnA : 0 ≤ ‖wordDeriv 3 α u x‖ := norm_nonneg _
    have hnnS : 0 ≤ ∑ i : Fin 3, ‖wordDeriv 3 (Fin.cons i γ) u x‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hmul :
        ‖wordDeriv 3 α u x‖ * ‖fderiv ℝ (wordDeriv 2 γ u) x‖ *
          ‖wordDeriv 1 β u x‖ ≤
        (‖wordDeriv 3 α u x‖ *
          ∑ i : Fin 3, ‖wordDeriv 3 (Fin.cons i γ) u x‖) * gradSup u := by
      have h1 : ‖wordDeriv 3 α u x‖ * ‖fderiv ℝ (wordDeriv 2 γ u) x‖ ≤
          ‖wordDeriv 3 α u x‖ * ∑ i : Fin 3, ‖wordDeriv 3 (Fin.cons i γ) u x‖ :=
        mul_le_mul_of_nonneg_left hop hnnA
      exact mul_le_mul h1 hω (norm_nonneg _) (mul_nonneg hnnA hnnS)
    have hamg : ‖wordDeriv 3 α u x‖ *
        ∑ i : Fin 3, ‖wordDeriv 3 (Fin.cons i γ) u x‖ ≤
          ‖wordDeriv 3 α u x‖ ^ 2 +
            3 * ∑ i : Fin 3, ‖wordDeriv 3 (Fin.cons i γ) u x‖ ^ 2 := by
      have h1 := mul_le_sq_add_sq (‖wordDeriv 3 α u x‖)
        (∑ i : Fin 3, ‖wordDeriv 3 (Fin.cons i γ) u x‖)
      have h2 : (∑ i : Fin 3, ‖wordDeriv 3 (Fin.cons i γ) u x‖) ^ 2 ≤
          3 * ∑ i : Fin 3, ‖wordDeriv 3 (Fin.cons i γ) u x‖ ^ 2 := by
        have := sq_sum_le_card_mul_sum_sq
          (s := (Finset.univ : Finset (Fin 3)))
          (f := fun i : Fin 3 => ‖wordDeriv 3 (Fin.cons i γ) u x‖)
        simpa [Finset.card_univ, Fintype.card_fin] using this
      nlinarith [h1, h2]
    have hscale :
        (‖wordDeriv 3 α u x‖ *
          ∑ i : Fin 3, ‖wordDeriv 3 (Fin.cons i γ) u x‖) * gradSup u ≤
          gradSup u *
            (‖wordDeriv 3 α u x‖ ^ 2 +
              3 * ∑ i : Fin 3, ‖wordDeriv 3 (Fin.cons i γ) u x‖ ^ 2) :=
      (mul_le_mul_of_nonneg_right hamg hgs0).trans_eq (by ring)
    exact (h.trans hmul).trans hscale
  have hmaj : Integrable (fun x =>
      gradSup u *
        (‖wordDeriv 3 α u x‖ ^ 2 +
          3 * ∑ i : Fin 3, ‖wordDeriv 3 (Fin.cons i γ) u x‖ ^ 2)) volume := by
    have hi := integrable_finset_sum (Finset.univ : Finset (Fin 3))
      (fun i _ => hsqi i)
    exact (hsqα.add (hi.const_mul 3)).const_mul (gradSup u)
  have hinter : Integrable
      (fun x => inner ℝ (wordDeriv 3 α u x)
        (convective (wordDeriv 1 β u) (wordDeriv 2 γ u) x)) volume :=
    hmaj.mono'
      ((contDiff_wordDeriv (k := 3) α hu).continuous.inner
        (contDiff_convective
          (contDiff_wordDeriv (k := 1) β hu)
          (contDiff_wordDeriv (k := 2) γ hu)).continuous).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using hpt x)
  have habs :
      |∫ x, inner ℝ (wordDeriv 3 α u x)
          (convective (wordDeriv 1 β u) (wordDeriv 2 γ u) x) ∂volume| ≤
        ∫ x, |inner ℝ (wordDeriv 3 α u x)
          (convective (wordDeriv 1 β u) (wordDeriv 2 γ u) x)| ∂volume := by
    simpa [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm
        (f := fun x => inner ℝ (wordDeriv 3 α u x)
          (convective (wordDeriv 1 β u) (wordDeriv 2 γ u) x)))
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun _ => abs_nonneg _) hmaj
    (Filter.Eventually.of_forall hpt)
  have hi := integrable_finset_sum (Finset.univ : Finset (Fin 3))
    (fun i _ => hsqi i)
  have hsumi := integral_finset_sum (Finset.univ : Finset (Fin 3))
    (fun i _ => hsqi i)
  have hrhs :
      ∫ x, gradSup u *
          (‖wordDeriv 3 α u x‖ ^ 2 +
            3 * ∑ i : Fin 3, ‖wordDeriv 3 (Fin.cons i γ) u x‖ ^ 2) ∂volume =
        gradSup u *
          (∫ x, ‖wordDeriv 3 α u x‖ ^ 2 ∂volume +
            3 * ∑ i : Fin 3,
              ∫ x, ‖wordDeriv 3 (Fin.cons i γ) u x‖ ^ 2 ∂volume) := by
    rw [integral_const_mul]
    congr 1
    have hf : Integrable (fun x => ‖wordDeriv 3 α u x‖ ^ 2) volume := hsqα
    have hg : Integrable (fun x =>
        3 * ∑ i : Fin 3, ‖wordDeriv 3 (Fin.cons i γ) u x‖ ^ 2) volume :=
      hi.const_mul 3
    have hfun : (fun x => ‖wordDeriv 3 α u x‖ ^ 2 +
          3 * ∑ i : Fin 3, ‖wordDeriv 3 (Fin.cons i γ) u x‖ ^ 2) =
        (fun x => ‖wordDeriv 3 α u x‖ ^ 2) +
          (fun x => 3 * ∑ i : Fin 3, ‖wordDeriv 3 (Fin.cons i γ) u x‖ ^ 2) := by
      ext x; simp [Pi.add_apply]
    rw [hfun]
    calc
      integral volume
          ((fun x => ‖wordDeriv 3 α u x‖ ^ 2) +
            (fun x => 3 * ∑ i : Fin 3, ‖wordDeriv 3 (Fin.cons i γ) u x‖ ^ 2))
          = ∫ x, ‖wordDeriv 3 α u x‖ ^ 2 +
              3 * ∑ i : Fin 3, ‖wordDeriv 3 (Fin.cons i γ) u x‖ ^ 2 ∂volume :=
            rfl
      _ = ∫ x, ‖wordDeriv 3 α u x‖ ^ 2 ∂volume +
            ∫ x, 3 * ∑ i : Fin 3, ‖wordDeriv 3 (Fin.cons i γ) u x‖ ^ 2 ∂volume :=
          integral_add hf hg
      _ = ∫ x, ‖wordDeriv 3 α u x‖ ^ 2 ∂volume +
            3 * ∫ x, ∑ i : Fin 3, ‖wordDeriv 3 (Fin.cons i γ) u x‖ ^ 2 ∂volume := by
          rw [integral_const_mul]
      _ = ∫ x, ‖wordDeriv 3 α u x‖ ^ 2 ∂volume +
            3 * ∑ i : Fin 3,
              ∫ x, ‖wordDeriv 3 (Fin.cons i γ) u x‖ ^ 2 ∂volume := by
          rw [hsumi]
  have hbound :
      gradSup u *
          (∫ x, ‖wordDeriv 3 α u x‖ ^ 2 ∂volume +
            3 * ∑ i : Fin 3,
              ∫ x, ‖wordDeriv 3 (Fin.cons i γ) u x‖ ^ 2 ∂volume) ≤
        10 * gradSup u * hsSq 3 u := by
    have h1 := integral_wordDeriv_sq_le hu hE (by norm_num : (3 : ℕ) ≤ 3) α
    have h2 : ∑ i : Fin 3,
        ∫ x, ‖wordDeriv 3 (Fin.cons i γ) u x‖ ^ 2 ∂volume ≤ 3 * hsSq 3 u := by
      have hterm : ∀ i : Fin 3,
          ∫ x, ‖wordDeriv 3 (Fin.cons i γ) u x‖ ^ 2 ∂volume ≤ hsSq 3 u :=
        fun i => integral_wordDeriv_sq_le hu hE (by norm_num : (3 : ℕ) ≤ 3)
          (Fin.cons i γ)
      have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3)))
        (fun i _ => hterm i)
      have hcard : ∑ _i : Fin 3, hsSq 3 u = 3 * hsSq 3 u := by
        simp [Finset.sum_const, Fintype.card_fin]
      exact hsum.trans_eq hcard
    have hE0 : 0 ≤ hsSq 3 u := ENNReal.toReal_nonneg
    have : ∫ x, ‖wordDeriv 3 α u x‖ ^ 2 ∂volume +
        3 * ∑ i : Fin 3,
          ∫ x, ‖wordDeriv 3 (Fin.cons i γ) u x‖ ^ 2 ∂volume ≤
        10 * hsSq 3 u := by
      nlinarith [h1, h2, hE0]
    calc
      _ ≤ gradSup u * (10 * hsSq 3 u) := mul_le_mul_of_nonneg_left this hgs0
      _ = 10 * gradSup u * hsSq 3 u := by ring
  exact habs.trans (hmono.trans_eq hrhs |>.trans hbound)

/-- Canonical Gagliardo–Nirenberg constant from `h3GagliardoNirenberg`. -/
noncomputable def h3GNConst : ℝ := Exists.choose h3GagliardoNirenberg

lemma h3GNConst_nonneg : 0 ≤ h3GNConst :=
  (Exists.choose_spec h3GagliardoNirenberg).1

lemma h3GN_le {u : VelocityField} (hu : ContDiff ℝ ∞ u)
    (hE : sobolevEnergy 3 u < ⊤) :
    ∑ (β : Fin 2 → Fin 3),
        ∫ x, ‖wordDeriv 2 β u x‖ ^ (4 : ℕ) ∂volume ≤
      h3GNConst * gradSup u ^ 2 * hsSq 3 u :=
  (Exists.choose_spec h3GagliardoNirenberg).2 u hu hE

lemma integral_abs_inner_convective_two_one_le {u : VelocityField}
    (hu : ContDiff ℝ ∞ u) (hE : sobolevEnergy 3 u < ⊤)
    (α : Fin 3 → Fin 3) (β : Fin 2 → Fin 3) (γ : Fin 1 → Fin 3) :
    |∫ x, inner ℝ (wordDeriv 3 α u x)
        (convective (wordDeriv 2 β u) (wordDeriv 1 γ u) x) ∂volume| ≤
      3 * (h3GNConst + 1) * gradSup u * hsSq 3 u := by
  have hC := h3GNConst_nonneg
  have hgn_u := h3GN_le hu hE
  set f := wordDeriv 3 α u
  set g := wordDeriv 2 β u
  have hd : Differentiable ℝ (wordDeriv 1 γ u) :=
    (contDiff_wordDeriv (k := 1) γ hu).differentiable (by simp)
  have hfc : Continuous f := (contDiff_wordDeriv (k := 3) α hu).continuous
  have hgc : Continuous g := (contDiff_wordDeriv (k := 2) β hu).continuous
  have hf2 := integrable_wordDeriv_sq hu hE (by norm_num : (3 : ℕ) ≤ 3) α
  have hgs0 : 0 ≤ gradSup u :=
    (norm_nonneg (fderiv ℝ u 0)).trans (le_gradSup hu hE 0)
  have hE0 : 0 ≤ hsSq 3 u := ENNReal.toReal_nonneg
  have hpt : ∀ x,
      |inner ℝ (f x) (convective g (wordDeriv 1 γ u) x)| ≤
        ∑ i : Fin 3, ‖f x‖ * ‖wordDeriv 2 (Fin.cons i γ) u x‖ * ‖g x‖ := by
    intro x
    have h1 := abs_inner_convective_le (v := f) (wvec := g)
      (f := wordDeriv 1 γ u) x (hd x)
    have hop := opNorm_fderiv_wordDeriv_one_le hu γ x
    have hnnf : 0 ≤ ‖f x‖ := norm_nonneg _
    have hnng : 0 ≤ ‖g x‖ := norm_nonneg _
    have hmul : ‖f x‖ * ‖fderiv ℝ (wordDeriv 1 γ u) x‖ * ‖g x‖ ≤
        ‖f x‖ * (∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i γ) u x‖) * ‖g x‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hop hnnf) hnng
    have hsum : ‖f x‖ *
        (∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i γ) u x‖) * ‖g x‖ =
        ∑ i : Fin 3, ‖f x‖ * ‖wordDeriv 2 (Fin.cons i γ) u x‖ * ‖g x‖ := by
      simp [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact h1.trans (hmul.trans_eq hsum)
  have hint_term : ∀ i : Fin 3,
      Integrable (fun x => ‖f x‖ * ‖wordDeriv 2 (Fin.cons i γ) u x‖ * ‖g x‖)
        volume := fun i =>
    integrable_norm_mul_mul hfc
      (contDiff_wordDeriv (k := 2) (Fin.cons i γ) hu).continuous hgc
      hf2 (integrable_wordDeriv_two_pow_four hu hE (Fin.cons i γ))
      (integrable_wordDeriv_two_pow_four hu hE β)
  have hmaj : Integrable
      (fun x => ∑ i : Fin 3,
        ‖f x‖ * ‖wordDeriv 2 (Fin.cons i γ) u x‖ * ‖g x‖) volume :=
    integrable_finset_sum _ (fun i _ => hint_term i)
  have hinter : Integrable
      (fun x => inner ℝ (f x) (convective g (wordDeriv 1 γ u) x)) volume :=
    hmaj.mono'
      (hfc.inner (contDiff_convective
        (contDiff_wordDeriv (k := 2) β hu)
        (contDiff_wordDeriv (k := 1) γ hu)).continuous).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs, f, g] using hpt x)
  have habs :
      |∫ x, inner ℝ (f x) (convective g (wordDeriv 1 γ u) x) ∂volume| ≤
        ∫ x, |inner ℝ (f x) (convective g (wordDeriv 1 γ u) x)| ∂volume := by
    simpa [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm
        (f := fun x => inner ℝ (f x) (convective g (wordDeriv 1 γ u) x)))
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun _ => abs_nonneg _) hmaj
    (Filter.Eventually.of_forall hpt)
  have hsum := integral_finset_sum (Finset.univ : Finset (Fin 3))
    (fun i _ => hint_term i)
  have hterm : ∀ i : Fin 3,
      ∫ x, ‖f x‖ * ‖wordDeriv 2 (Fin.cons i γ) u x‖ * ‖g x‖ ∂volume ≤
        (h3GNConst + 1) * gradSup u * hsSq 3 u := by
    intro i
    have hholder := integral_norm_mul_mul_le_L2_L4_L4 hfc
      (contDiff_wordDeriv (k := 2) (Fin.cons i γ) hu).continuous hgc
      hf2 (integrable_wordDeriv_two_pow_four hu hE (Fin.cons i γ))
      (integrable_wordDeriv_two_pow_four hu hE β)
    have hfbound := integral_wordDeriv_sq_le hu hE
      (by norm_num : (3 : ℕ) ≤ 3) α
    have hAbound := integral_wordDeriv_two_pow_four_le hu hE
      (Fin.cons i γ) hC hgn_u
    have hBbound := integral_wordDeriv_two_pow_four_le hu hE β hC hgn_u
    have hfnn : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂volume :=
      integral_nonneg fun _ => sq_nonneg _
    have hAnn : 0 ≤ ∫ x, ‖wordDeriv 2 (Fin.cons i γ) u x‖ ^ (4 : ℕ) ∂volume :=
      integral_nonneg fun _ => pow_nonneg (norm_nonneg _) _
    have hBnn : 0 ≤ ∫ x, ‖g x‖ ^ (4 : ℕ) ∂volume :=
      integral_nonneg fun _ => pow_nonneg (norm_nonneg _) _
    have hB0 : 0 ≤ h3GNConst * gradSup u ^ 2 * hsSq 3 u :=
      mul_nonneg (mul_nonneg hC (sq_nonneg _)) hE0
    have hsqrtf : Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂volume) ≤ Real.sqrt (hsSq 3 u) :=
      Real.sqrt_le_sqrt hfbound
    have hprod := rpow_quarter_prod_le hAnn hBnn hB0 hAbound hBbound
    have : Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂volume) *
        Real.sqrt (Real.sqrt (∫ x, ‖wordDeriv 2 (Fin.cons i γ) u x‖ ^ (4 : ℕ)
            ∂volume) *
          Real.sqrt (∫ x, ‖g x‖ ^ (4 : ℕ) ∂volume)) ≤
        Real.sqrt (hsSq 3 u) * Real.sqrt (h3GNConst * gradSup u ^ 2 * hsSq 3 u) :=
      mul_le_mul hsqrtf hprod (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    exact hholder.trans (this.trans (sqrt_mul_energy_le h3GNConst (gradSup u) (hsSq 3 u)
      hC hgs0 hE0))
  have hsumle :
      ∑ i : Fin 3,
          ∫ x, ‖f x‖ * ‖wordDeriv 2 (Fin.cons i γ) u x‖ * ‖g x‖ ∂volume ≤
        3 * (h3GNConst + 1) * gradSup u * hsSq 3 u := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3)))
      (fun i _ => hterm i)
    have hcard : ∑ _i : Fin 3, (h3GNConst + 1) * gradSup u * hsSq 3 u =
        3 * ((h3GNConst + 1) * gradSup u * hsSq 3 u) := by
      simp [Finset.sum_const, Fintype.card_fin]
    have := h.trans_eq hcard
    simpa [mul_assoc] using this
  exact habs.trans (hmono.trans (hsum.trans_le hsumle))


lemma integrable_inner_convective_three_zero {u : VelocityField}
    (hu : ContDiff ℝ ∞ u) (hE : sobolevEnergy 3 u < ⊤) (α : Fin 3 → Fin 3) :
    Integrable (fun x => inner ℝ (wordDeriv 3 α u x)
      (convective (wordDeriv 3 α u) u x)) volume := by
  have hsq := integrable_wordDeriv_sq hu hE (by norm_num : (3 : ℕ) ≤ 3) α
  have hpt : ∀ x,
      |inner ℝ (wordDeriv 3 α u x) (convective (wordDeriv 3 α u) u x)| ≤
        gradSup u * ‖wordDeriv 3 α u x‖ ^ 2 := by
    intro x
    have h := abs_inner_convective_le (v := wordDeriv 3 α u)
      (wvec := wordDeriv 3 α u) (f := u) x ((hu.differentiable (by simp)) x)
    have hgs := le_gradSup hu hE x
    nlinarith [hgs, norm_nonneg (wordDeriv 3 α u x),
      norm_nonneg (fderiv ℝ u x)]
  refine (hsq.const_mul (gradSup u)).mono' ?_
    (Filter.Eventually.of_forall fun x => ?_)
  · exact ((contDiff_wordDeriv (k := 3) α hu).continuous.inner
      (contDiff_convective (contDiff_wordDeriv (k := 3) α hu) hu).continuous).aestronglyMeasurable
  · simpa [Real.norm_eq_abs] using hpt x

lemma integrable_inner_convective_one_two {u : VelocityField}
    (hu : ContDiff ℝ ∞ u) (hE : sobolevEnergy 3 u < ⊤)
    (α : Fin 3 → Fin 3) (β : Fin 1 → Fin 3) (γ : Fin 2 → Fin 3) :
    Integrable (fun x => inner ℝ (wordDeriv 3 α u x)
      (convective (wordDeriv 1 β u) (wordDeriv 2 γ u) x)) volume := by
  have hsqα := integrable_wordDeriv_sq hu hE (by norm_num : (3 : ℕ) ≤ 3) α
  have hsqi : ∀ i : Fin 3,
      Integrable (fun x => ‖wordDeriv 3 (Fin.cons i γ) u x‖ ^ 2) volume :=
    fun i => integrable_wordDeriv_sq hu hE (by norm_num : (3 : ℕ) ≤ 3)
      (Fin.cons i γ)
  have hi := integrable_finset_sum (Finset.univ : Finset (Fin 3))
    (fun i _ => hsqi i)
  have hgs0 : 0 ≤ gradSup u :=
    (norm_nonneg (fderiv ℝ u 0)).trans (le_gradSup hu hE 0)
  have hd : Differentiable ℝ (wordDeriv 2 γ u) :=
    (contDiff_wordDeriv (k := 2) γ hu).differentiable (by simp)
  have hpt : ∀ x,
      |inner ℝ (wordDeriv 3 α u x)
        (convective (wordDeriv 1 β u) (wordDeriv 2 γ u) x)| ≤
        gradSup u *
          (‖wordDeriv 3 α u x‖ ^ 2 +
            3 * ∑ i : Fin 3, ‖wordDeriv 3 (Fin.cons i γ) u x‖ ^ 2) := by
    intro x
    have h := abs_inner_convective_le (v := wordDeriv 3 α u)
      (wvec := wordDeriv 1 β u) (f := wordDeriv 2 γ u) x (hd x)
    have hop := opNorm_fderiv_wordDeriv_two_le hu γ x
    have hω := (norm_wordDeriv_one_le β u x).trans (le_gradSup hu hE x)
    have hnnA : 0 ≤ ‖wordDeriv 3 α u x‖ := norm_nonneg _
    have hnnS : 0 ≤ ∑ i : Fin 3, ‖wordDeriv 3 (Fin.cons i γ) u x‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have h1 : ‖wordDeriv 3 α u x‖ * ‖fderiv ℝ (wordDeriv 2 γ u) x‖ ≤
        ‖wordDeriv 3 α u x‖ * ∑ i : Fin 3, ‖wordDeriv 3 (Fin.cons i γ) u x‖ :=
      mul_le_mul_of_nonneg_left hop hnnA
    have hmul := mul_le_mul h1 hω (norm_nonneg _) (mul_nonneg hnnA hnnS)
    have hamg : ‖wordDeriv 3 α u x‖ *
        ∑ i : Fin 3, ‖wordDeriv 3 (Fin.cons i γ) u x‖ ≤
          ‖wordDeriv 3 α u x‖ ^ 2 +
            3 * ∑ i : Fin 3, ‖wordDeriv 3 (Fin.cons i γ) u x‖ ^ 2 := by
      have ha := mul_le_sq_add_sq (‖wordDeriv 3 α u x‖)
        (∑ i : Fin 3, ‖wordDeriv 3 (Fin.cons i γ) u x‖)
      have hb : (∑ i : Fin 3, ‖wordDeriv 3 (Fin.cons i γ) u x‖) ^ 2 ≤
          3 * ∑ i : Fin 3, ‖wordDeriv 3 (Fin.cons i γ) u x‖ ^ 2 := by
        have := sq_sum_le_card_mul_sum_sq
          (s := (Finset.univ : Finset (Fin 3)))
          (f := fun i : Fin 3 => ‖wordDeriv 3 (Fin.cons i γ) u x‖)
        simpa [Finset.card_univ, Fintype.card_fin] using this
      nlinarith [ha, hb]
    have hscale :
        (‖wordDeriv 3 α u x‖ *
          ∑ i : Fin 3, ‖wordDeriv 3 (Fin.cons i γ) u x‖) * gradSup u ≤
          gradSup u *
            (‖wordDeriv 3 α u x‖ ^ 2 +
              3 * ∑ i : Fin 3, ‖wordDeriv 3 (Fin.cons i γ) u x‖ ^ 2) :=
      (mul_le_mul_of_nonneg_right hamg hgs0).trans_eq (by ring)
    exact (h.trans hmul).trans hscale
  have hmaj : Integrable (fun x =>
      gradSup u *
        (‖wordDeriv 3 α u x‖ ^ 2 +
          3 * ∑ i : Fin 3, ‖wordDeriv 3 (Fin.cons i γ) u x‖ ^ 2)) volume :=
    (hsqα.add (hi.const_mul 3)).const_mul (gradSup u)
  exact hmaj.mono'
    ((contDiff_wordDeriv (k := 3) α hu).continuous.inner
      (contDiff_convective (contDiff_wordDeriv (k := 1) β hu)
        (contDiff_wordDeriv (k := 2) γ hu)).continuous).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hpt x)

lemma integrable_inner_convective_two_one {u : VelocityField}
    (hu : ContDiff ℝ ∞ u) (hE : sobolevEnergy 3 u < ⊤)
    (α : Fin 3 → Fin 3) (β : Fin 2 → Fin 3) (γ : Fin 1 → Fin 3) :
    Integrable (fun x => inner ℝ (wordDeriv 3 α u x)
      (convective (wordDeriv 2 β u) (wordDeriv 1 γ u) x)) volume := by
  have hf2 := integrable_wordDeriv_sq hu hE (by norm_num : (3 : ℕ) ≤ 3) α
  have hd : Differentiable ℝ (wordDeriv 1 γ u) :=
    (contDiff_wordDeriv (k := 1) γ hu).differentiable (by simp)
  have hpt : ∀ x,
      |inner ℝ (wordDeriv 3 α u x)
        (convective (wordDeriv 2 β u) (wordDeriv 1 γ u) x)| ≤
        ∑ i : Fin 3, ‖wordDeriv 3 α u x‖ *
          ‖wordDeriv 2 (Fin.cons i γ) u x‖ * ‖wordDeriv 2 β u x‖ := by
    intro x
    have h1 := abs_inner_convective_le (v := wordDeriv 3 α u)
      (wvec := wordDeriv 2 β u) (f := wordDeriv 1 γ u) x (hd x)
    have hop := opNorm_fderiv_wordDeriv_one_le hu γ x
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hop (norm_nonneg (wordDeriv 3 α u x)))
      (norm_nonneg (wordDeriv 2 β u x))
    have hsum : ‖wordDeriv 3 α u x‖ *
        (∑ i : Fin 3, ‖wordDeriv 2 (Fin.cons i γ) u x‖) *
        ‖wordDeriv 2 β u x‖ =
        ∑ i : Fin 3, ‖wordDeriv 3 α u x‖ *
          ‖wordDeriv 2 (Fin.cons i γ) u x‖ * ‖wordDeriv 2 β u x‖ := by
      simp [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact h1.trans (hmul.trans_eq hsum)
  have hint_term : ∀ i : Fin 3,
      Integrable (fun x => ‖wordDeriv 3 α u x‖ *
        ‖wordDeriv 2 (Fin.cons i γ) u x‖ * ‖wordDeriv 2 β u x‖) volume :=
    fun i => integrable_norm_mul_mul
      (contDiff_wordDeriv (k := 3) α hu).continuous
      (contDiff_wordDeriv (k := 2) (Fin.cons i γ) hu).continuous
      (contDiff_wordDeriv (k := 2) β hu).continuous hf2
      (integrable_wordDeriv_two_pow_four hu hE (Fin.cons i γ))
      (integrable_wordDeriv_two_pow_four hu hE β)
  have hmaj := integrable_finset_sum (Finset.univ : Finset (Fin 3))
    (fun i _ => hint_term i)
  exact hmaj.mono'
    ((contDiff_wordDeriv (k := 3) α hu).continuous.inner
      (contDiff_convective (contDiff_wordDeriv (k := 2) β hu)
        (contDiff_wordDeriv (k := 1) γ hu)).continuous).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hpt x)

theorem abs_integral_commutator_order_zero {u : VelocityField}
    (α : Fin 0 → Fin 3) :
    |∫ x, inner ℝ (wordDeriv 0 α u x) (convectiveCommutator 0 α u x) ∂volume| =
      0 := by
  simp [convectiveCommutator_zero, inner_zero_right, integral_zero]

theorem abs_integral_commutator_order_three {u : VelocityField}
    (hu : ContDiff ℝ ∞ u) (hE : sobolevEnergy 3 u < ⊤) (α : Fin 3 → Fin 3) :
    |∫ x, inner ℝ (wordDeriv 3 α u x) (convectiveCommutator 3 α u x) ∂volume| ≤
      (31 + 9 * (h3GNConst + 1)) * gradSup u * hsSq 3 u := by
  set D3 := wordDeriv 3 α u
  set t1 := convective D3 u
  set t2 := convective (wordDeriv 2 (Fin.tail α) u)
      (wordDeriv 1 (fun _ : Fin 1 => α 0) u)
  set t3 := convective
      (wordDeriv 2 (Fin.cons (α 0) (Fin.tail (Fin.tail α))) u)
      (wordDeriv 1 (fun _ : Fin 1 => (Fin.tail α) 0) u)
  set t4 := convective (wordDeriv 1 (Fin.tail (Fin.tail α)) u)
      (wordDeriv 2 (Fin.cons (α 0) (fun _ : Fin 1 => (Fin.tail α) 0)) u)
  set t5 := convective
      (wordDeriv 2 (Fin.cons (α 0) (fun _ : Fin 1 => (Fin.tail α) 0)) u)
      (wordDeriv 1 (Fin.tail (Fin.tail α)) u)
  set t6 := convective (wordDeriv 1 (fun _ : Fin 1 => (Fin.tail α) 0) u)
      (wordDeriv 2 (Fin.cons (α 0) (Fin.tail (Fin.tail α))) u)
  set t7 := convective (wordDeriv 1 (fun _ : Fin 1 => α 0) u)
      (wordDeriv 2 (Fin.tail α) u)
  have hcomm : convectiveCommutator 3 α u = t1 + t2 + t3 + t4 + t5 + t6 + t7 := by
    funext x
    simpa [D3, t1, t2, t3, t4, t5, t6, t7, Pi.add_apply] using
      convectiveCommutator_order_three hu α x
  set i1 := fun x => inner ℝ (D3 x) (t1 x)
  set i2 := fun x => inner ℝ (D3 x) (t2 x)
  set i3 := fun x => inner ℝ (D3 x) (t3 x)
  set i4 := fun x => inner ℝ (D3 x) (t4 x)
  set i5 := fun x => inner ℝ (D3 x) (t5 x)
  set i6 := fun x => inner ℝ (D3 x) (t6 x)
  set i7 := fun x => inner ℝ (D3 x) (t7 x)
  have hinner : (fun x => inner ℝ (D3 x) (convectiveCommutator 3 α u x)) =
      i1 + i2 + i3 + i4 + i5 + i6 + i7 := by
    funext x
    simp only [hcomm, i1, i2, i3, i4, i5, i6, i7, Pi.add_apply, inner_add_right]
    try abel
  have hi1 : Integrable i1 volume := by
    dsimp [i1, D3, t1]
    exact integrable_inner_convective_three_zero hu hE α
  have hi2 : Integrable i2 volume := by
    dsimp [i2, D3, t2]
    exact integrable_inner_convective_two_one hu hE α (Fin.tail α)
      (fun _ : Fin 1 => α 0)
  have hi3 : Integrable i3 volume := by
    dsimp [i3, D3, t3]
    exact integrable_inner_convective_two_one hu hE α
      (Fin.cons (α 0) (Fin.tail (Fin.tail α)))
      (fun _ : Fin 1 => (Fin.tail α) 0)
  have hi4 : Integrable i4 volume := by
    dsimp [i4, D3, t4]
    exact integrable_inner_convective_one_two hu hE α (Fin.tail (Fin.tail α))
      (Fin.cons (α 0) (fun _ : Fin 1 => (Fin.tail α) 0))
  have hi5 : Integrable i5 volume := by
    dsimp [i5, D3, t5]
    exact integrable_inner_convective_two_one hu hE α
      (Fin.cons (α 0) (fun _ : Fin 1 => (Fin.tail α) 0))
      (Fin.tail (Fin.tail α))
  have hi6 : Integrable i6 volume := by
    dsimp [i6, D3, t6]
    exact integrable_inner_convective_one_two hu hE α
      (fun _ : Fin 1 => (Fin.tail α) 0)
      (Fin.cons (α 0) (Fin.tail (Fin.tail α)))
  have hi7 : Integrable i7 volume := by
    dsimp [i7, D3, t7]
    exact integrable_inner_convective_one_two hu hE α
      (fun _ : Fin 1 => α 0) (Fin.tail α)
  have hsumI :
      ∫ x, inner ℝ (D3 x) (convectiveCommutator 3 α u x) ∂volume =
        ∫ x, i1 x ∂volume + ∫ x, i2 x ∂volume + ∫ x, i3 x ∂volume +
          ∫ x, i4 x ∂volume + ∫ x, i5 x ∂volume + ∫ x, i6 x ∂volume +
            ∫ x, i7 x ∂volume := by
    have I12 : Integrable (i1 + i2) volume := hi1.add hi2
    have I13 : Integrable (i1 + i2 + i3) volume := I12.add hi3
    have I14 : Integrable (i1 + i2 + i3 + i4) volume := I13.add hi4
    have I15 : Integrable (i1 + i2 + i3 + i4 + i5) volume := I14.add hi5
    have I16 : Integrable (i1 + i2 + i3 + i4 + i5 + i6) volume := I15.add hi6
    rw [hinner]
    calc
      integral volume (i1 + i2 + i3 + i4 + i5 + i6 + i7)
          = ∫ x, (i1 + i2 + i3 + i4 + i5 + i6) x + i7 x ∂volume := rfl
      _ = ∫ x, (i1 + i2 + i3 + i4 + i5 + i6) x ∂volume + ∫ x, i7 x ∂volume :=
          integral_add I16 hi7
      _ = ∫ x, (i1 + i2 + i3 + i4 + i5) x + i6 x ∂volume + ∫ x, i7 x ∂volume := by
          congr 2
      _ = ∫ x, (i1 + i2 + i3 + i4 + i5) x ∂volume + ∫ x, i6 x ∂volume +
            ∫ x, i7 x ∂volume := by
          rw [integral_add I15 hi6]
      _ = ∫ x, (i1 + i2 + i3 + i4) x + i5 x ∂volume + ∫ x, i6 x ∂volume +
            ∫ x, i7 x ∂volume := rfl
      _ = ∫ x, (i1 + i2 + i3 + i4) x ∂volume + ∫ x, i5 x ∂volume +
            ∫ x, i6 x ∂volume + ∫ x, i7 x ∂volume := by
          rw [integral_add I14 hi5]
      _ = ∫ x, (i1 + i2 + i3) x + i4 x ∂volume + ∫ x, i5 x ∂volume +
            ∫ x, i6 x ∂volume + ∫ x, i7 x ∂volume := rfl
      _ = ∫ x, (i1 + i2 + i3) x ∂volume + ∫ x, i4 x ∂volume +
            ∫ x, i5 x ∂volume + ∫ x, i6 x ∂volume + ∫ x, i7 x ∂volume := by
          rw [integral_add I13 hi4]
      _ = ∫ x, (i1 + i2) x + i3 x ∂volume + ∫ x, i4 x ∂volume +
            ∫ x, i5 x ∂volume + ∫ x, i6 x ∂volume + ∫ x, i7 x ∂volume := rfl
      _ = ∫ x, (i1 + i2) x ∂volume + ∫ x, i3 x ∂volume +
            ∫ x, i4 x ∂volume + ∫ x, i5 x ∂volume + ∫ x, i6 x ∂volume +
            ∫ x, i7 x ∂volume := by
          rw [integral_add I12 hi3]
      _ = ∫ x, i1 x + i2 x ∂volume + ∫ x, i3 x ∂volume +
            ∫ x, i4 x ∂volume + ∫ x, i5 x ∂volume + ∫ x, i6 x ∂volume +
            ∫ x, i7 x ∂volume := rfl
      _ = ∫ x, i1 x ∂volume + ∫ x, i2 x ∂volume + ∫ x, i3 x ∂volume +
            ∫ x, i4 x ∂volume + ∫ x, i5 x ∂volume + ∫ x, i6 x ∂volume +
            ∫ x, i7 x ∂volume := by
          rw [integral_add hi1 hi2]
  have b1 := integral_abs_inner_convective_three_zero_le hu hE α
  have b2 := integral_abs_inner_convective_two_one_le hu hE α
    (Fin.tail α) (fun _ : Fin 1 => α 0)
  have b3 := integral_abs_inner_convective_two_one_le hu hE α
    (Fin.cons (α 0) (Fin.tail (Fin.tail α)))
    (fun _ : Fin 1 => (Fin.tail α) 0)
  have b4 := integral_abs_inner_convective_one_two_le hu hE α
    (Fin.tail (Fin.tail α))
    (Fin.cons (α 0) (fun _ : Fin 1 => (Fin.tail α) 0))
  have b5 := integral_abs_inner_convective_two_one_le hu hE α
    (Fin.cons (α 0) (fun _ : Fin 1 => (Fin.tail α) 0))
    (Fin.tail (Fin.tail α))
  have b6 := integral_abs_inner_convective_one_two_le hu hE α
    (fun _ : Fin 1 => (Fin.tail α) 0)
    (Fin.cons (α 0) (Fin.tail (Fin.tail α)))
  have b7 := integral_abs_inner_convective_one_two_le hu hE α
    (fun _ : Fin 1 => α 0) (Fin.tail α)
  have habs := abs_add_seven
    (∫ x, i1 x ∂volume) (∫ x, i2 x ∂volume) (∫ x, i3 x ∂volume)
    (∫ x, i4 x ∂volume) (∫ x, i5 x ∂volume) (∫ x, i6 x ∂volume)
    (∫ x, i7 x ∂volume)
  have hC0 : 0 ≤ h3GNConst := h3GNConst_nonneg
  have hgs0 : 0 ≤ gradSup u :=
    (norm_nonneg (fderiv ℝ u 0)).trans (le_gradSup hu hE 0)
  have hE0 : 0 ≤ hsSq 3 u := ENNReal.toReal_nonneg
  have hsumbound :
      |∫ x, i1 x ∂volume| + |∫ x, i2 x ∂volume| + |∫ x, i3 x ∂volume| +
        |∫ x, i4 x ∂volume| + |∫ x, i5 x ∂volume| + |∫ x, i6 x ∂volume| +
        |∫ x, i7 x ∂volume| ≤
      (31 + 9 * (h3GNConst + 1)) * gradSup u * hsSq 3 u := by
    -- b1 ≤ 1 * g * E; b2,b3,b5 ≤ 3(C+1) g E; b4,b6,b7 ≤ 10 g E
    have : |∫ x, i1 x ∂volume| ≤ gradSup u * hsSq 3 u := by
      simpa [D3, t1, i1] using b1
    have h2' : |∫ x, i2 x ∂volume| ≤
        3 * (h3GNConst + 1) * gradSup u * hsSq 3 u := by
      simpa [D3, t2, i2] using b2
    have h3' : |∫ x, i3 x ∂volume| ≤
        3 * (h3GNConst + 1) * gradSup u * hsSq 3 u := by
      simpa [D3, t3, i3] using b3
    have h4' : |∫ x, i4 x ∂volume| ≤ 10 * gradSup u * hsSq 3 u := by
      simpa [D3, t4, i4] using b4
    have h5' : |∫ x, i5 x ∂volume| ≤
        3 * (h3GNConst + 1) * gradSup u * hsSq 3 u := by
      simpa [D3, t5, i5] using b5
    have h6' : |∫ x, i6 x ∂volume| ≤ 10 * gradSup u * hsSq 3 u := by
      simpa [D3, t6, i6] using b6
    have h7' : |∫ x, i7 x ∂volume| ≤ 10 * gradSup u * hsSq 3 u := by
      simpa [D3, t7, i7] using b7
    nlinarith [this, h2', h3', h4', h5', h6', h7', hC0, hgs0, hE0]
  rw [hsumI]
  exact habs.trans hsumbound

lemma card_words (k : ℕ) : Fintype.card (Fin k → Fin 3) = 3 ^ k := by
  simp [Fintype.card_fun, Fintype.card_fin]

theorem h3CommutatorEstimate : H3CommutatorEstimate := by
  let C : ℝ :=
    3 + 9 * 28 + 27 * (31 + 9 * (h3GNConst + 1))
  have hC : 0 ≤ C := by
    have : 0 ≤ h3GNConst := h3GNConst_nonneg
    nlinarith
  refine ⟨C, hC, ?_⟩
  intro u hu hE
  have hgs0 : 0 ≤ gradSup u :=
    (norm_nonneg (fderiv ℝ u 0)).trans (le_gradSup hu hE 0)
  have hE0 : 0 ≤ hsSq 3 u := ENNReal.toReal_nonneg
  have h0 : ∀ α : Fin 0 → Fin 3,
      |∫ x, inner ℝ (wordDeriv 0 α u x)
        (convectiveCommutator 0 α u x) ∂volume| ≤
        0 * gradSup u * hsSq 3 u := fun α => by
    simp [abs_integral_commutator_order_zero α]
  have h1 : ∀ α : Fin 1 → Fin 3,
      |∫ x, inner ℝ (wordDeriv 1 α u x)
        (convectiveCommutator 1 α u x) ∂volume| ≤
        gradSup u * hsSq 3 u := fun α =>
    (abs_integral_commutator_order_one hu hE α).trans
      (mul_le_mul_of_nonneg_left
        (integral_wordDeriv_sq_le hu hE (by norm_num : (1 : ℕ) ≤ 3) α) hgs0)
  have h2 : ∀ α : Fin 2 → Fin 3,
      |∫ x, inner ℝ (wordDeriv 2 α u x)
        (convectiveCommutator 2 α u x) ∂volume| ≤
        28 * gradSup u * hsSq 3 u :=
    fun α => abs_integral_commutator_order_two hu hE α
  have h3 : ∀ α : Fin 3 → Fin 3,
      |∫ x, inner ℝ (wordDeriv 3 α u x)
        (convectiveCommutator 3 α u x) ∂volume| ≤
        (31 + 9 * (h3GNConst + 1)) * gradSup u * hsSq 3 u :=
    fun α => abs_integral_commutator_order_three hu hE α
  have htri :
      |∑ k ∈ Finset.range 4, ∑ α : Fin k → Fin 3,
          ∫ x, inner ℝ (wordDeriv k α u x)
            (convectiveCommutator k α u x) ∂volume| ≤
        ∑ k ∈ Finset.range 4, ∑ α : Fin k → Fin 3,
          |∫ x, inner ℝ (wordDeriv k α u x)
            (convectiveCommutator k α u x) ∂volume| :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _)
  have hsum0 :
      ∑ α : Fin 0 → Fin 3,
          |∫ x, inner ℝ (wordDeriv 0 α u x)
            (convectiveCommutator 0 α u x) ∂volume| ≤ 0 := by
    have h0' : ∀ α : Fin 0 → Fin 3,
        |∫ x, inner ℝ (wordDeriv 0 α u x)
          (convectiveCommutator 0 α u x) ∂volume| ≤ 0 := fun α =>
      (h0 α).trans_eq (by ring)
    have := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 0 → Fin 3)))
      (fun α _ => h0' α)
    have hcard : ∑ _α : Fin 0 → Fin 3, (0 : ℝ) = 0 := by
      simp [Finset.sum_const]
    exact this.trans_eq hcard
  have hsum1 :
      ∑ α : Fin 1 → Fin 3,
          |∫ x, inner ℝ (wordDeriv 1 α u x)
            (convectiveCommutator 1 α u x) ∂volume| ≤
        3 * gradSup u * hsSq 3 u := by
    have := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 1 → Fin 3)))
      (fun α _ => h1 α)
    have hcard : ∑ _α : Fin 1 → Fin 3, gradSup u * hsSq 3 u =
        3 * (gradSup u * hsSq 3 u) := by
      simp [Finset.sum_const, card_words]
    exact this.trans_eq (by simpa [mul_assoc] using hcard)
  have hsum2 :
      ∑ α : Fin 2 → Fin 3,
          |∫ x, inner ℝ (wordDeriv 2 α u x)
            (convectiveCommutator 2 α u x) ∂volume| ≤
        9 * 28 * gradSup u * hsSq 3 u := by
    have := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 2 → Fin 3)))
      (fun α _ => h2 α)
    have hcard : ∑ _α : Fin 2 → Fin 3, 28 * gradSup u * hsSq 3 u =
        9 * (28 * gradSup u * hsSq 3 u) := by
      simp [Finset.sum_const, card_words]
    exact this.trans_eq (by simpa [mul_assoc] using hcard)
  have hsum3 :
      ∑ α : Fin 3 → Fin 3,
          |∫ x, inner ℝ (wordDeriv 3 α u x)
            (convectiveCommutator 3 α u x) ∂volume| ≤
        27 * (31 + 9 * (h3GNConst + 1)) * gradSup u * hsSq 3 u := by
    have := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3 → Fin 3)))
      (fun α _ => h3 α)
    have hcard :
        ∑ _α : Fin 3 → Fin 3,
            (31 + 9 * (h3GNConst + 1)) * gradSup u * hsSq 3 u =
          27 * ((31 + 9 * (h3GNConst + 1)) * gradSup u * hsSq 3 u) := by
      simp [Finset.sum_const, card_words]
    exact this.trans_eq (by simpa [mul_assoc] using hcard)
  have hparts :
      ∑ k ∈ Finset.range 4, ∑ α : Fin k → Fin 3,
          |∫ x, inner ℝ (wordDeriv k α u x)
            (convectiveCommutator k α u x) ∂volume| ≤
        C * gradSup u * hsSq 3 u := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one]
    -- range 4 = {0,1,2,3}; sum_range_one is {0}
    nlinarith [hsum0, hsum1, hsum2, hsum3, hC, hgs0, hE0]
  exact htri.trans hparts

/-- `katoPonce_h3_energy` with `H3CommutatorEstimate` discharged
by `h3CommutatorEstimate`. The remaining hypotheses are viscosity
nonnegativity, a Fefferman-class solution, finite H³ energy on `Ico 0 T`,
the H³ energy right-derivative formula, partial commutation, and
vanishing IBP flux. -/
theorem katoPonce_h3_energy' :
    ∃ Ck : ℝ, 0 ≤ Ck ∧
      ∀ (ν T : ℝ) (u₀ : VelocityField) (u : TimeDependentVelocity)
        (p : TimeDependentPressure),
        0 ≤ ν →
        IsFeffermanSolutionOn ν T u₀ u p →
        (∀ t ∈ Ico (0 : ℝ) T, sobolevEnergy 3 (u t) < ⊤) →
        H3EnergyRightDerivativeFormula T u →
        (∀ t ∈ Ico (0 : ℝ) T, H3PartialCommutation (u t) (p t)) →
        (∀ t ∈ Ico (0 : ℝ) T, H3IBPVanishingFlux (u t) (p t)) →
        ∀ s ∈ Ico (0 : ℝ) T,
          ∃ d : ℝ, HasDerivWithinAt (fun t => hsSq 3 (u t)) d (Ici s) s ∧
            d ≤ Ck * gradSup (u s) * hsSq 3 (u s) :=
  katoPonce_h3_energy h3CommutatorEstimate

#print axioms KatoPonceCommutator.convectiveCommutator_order_one
#print axioms KatoPonceCommutator.norm_convectiveCommutator_order_one
#print axioms KatoPonceCommutator.abs_integral_commutator_order_one
#print axioms KatoPonceCommutator.integral_gradNormSq_sq
#print axioms KatoPonceCommutator.integral_gradNormSq_sq_le_of_hasCompactSupport
#print axioms KatoPonceCommutator.partiali2_cutoff
#print axioms KatoPonceCommutator.h3GagliardoNirenberg
#print axioms KatoPonceCommutator.abs_integral_commutator_order_two
#print axioms KatoPonceCommutator.abs_integral_commutator_order_three
#print axioms KatoPonceCommutator.h3CommutatorEstimate
#print axioms KatoPonceCommutator.katoPonce_h3_energy'

end KatoPonceCommutator
