import Scratch.KatoPonce
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # The H³ Kato commutator estimate

This file proves (or, where a remaining analytic input is still named, reduces)
`KatoPonce.H3CommutatorEstimate`: there is `C ≥ 0` such that for every
`C^∞` field with finite H³ energy,

`|∑_{|α|≤3} ∫ ⟨∂^α u, [∂^α, u·∇]u⟩| ≤ C ‖∇u‖_∞ ‖u‖²_{H³}`.

What is proved here: the first-order Leibniz identification
`[∂ᵢ, u·∇]u = (∂ᵢ u)·∇u` (including the `ContDiff 2 ≤ ∞` unification), the
pointwise bound `‖[∂ᵢ, u·∇]u‖ ≤ ‖∇u‖ ‖∂ᵢ u‖`, and the integral pairing bound
`|∫ ⟨∂ᵢ u, [∂ᵢ, u·∇]u⟩| ≤ ‖∇u‖_∞ ∫ |∂ᵢ u|²`. The order-zero commutator is
already `convectiveCommutator_zero` in `KatoPonce`.

What remains for `H3CommutatorEstimate` itself: the Gagliardo–Nirenberg
interpolation `‖∂²u‖₄² ≲ ‖∇u‖_∞ ‖u‖_{H³}` (named `H3GagliardoNirenberg`
below), the Leibniz expansion and Hölder bounds for `|α| = 2, 3` (the
`|α| = 3`, `|β| = 2` term is the one that needs GN), and the assembly.
A Fourier-side product estimate would bound by `‖û‖` norms, which do not
imply the `‖∇u‖_∞` form, so it is not used here. (`GradBound` already
gives `‖∇u‖_∞ ≲ ‖u‖_{H³}` and `BddAbove`, which we do use.)

The GN interpolation, for a general `C^∞` field with only finite H³
energy, needs a cutoff or vanishing-flux argument to justify
`∫ |∇φ|⁴ = -∫ φ (Δφ |∇φ|² + 2 ∇φ · (Hess φ ∇φ))` on ℝ³. That IBP is not
supplied by `ContDiff ∞` + `sobolevEnergy 3 u < ⊤` alone, and is not
yet formalized in this repository. The statement of
`H3CommutatorEstimate` is not weakened; it remains a named `Prop` in
`KatoPonce.lean`, and `katoPonce_h3_energy` still takes it as a
hypothesis.

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

/-! ## Remaining analytic input -/

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

end KatoPonceCommutator
