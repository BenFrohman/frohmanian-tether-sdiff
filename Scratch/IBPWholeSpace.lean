import FrohmanianTether.NS_Equations
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! # Whole-space integration by parts on ℝ³

`T3` is `EuclideanSpace ℝ (Fin 3)`, i.e. the physical domain ℝ³ (not a torus).
Mathlib already has whole-space IBP for integrable functions, with no decay
or cutoff hypothesis:

* `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`
* `integral_bilinear_fderiv_right_eq_neg_left_of_integrable`
  (and the `hasFDerivAt` form)

These are stated on a real normed space `E` with an arbitrary measure `μ`,
so they apply to `T3` with Haar/`MeasureTheory.volume`
(definitionally `NavierStokes3D.volume`). The only inputs are
differentiability (here: everywhere, so in particular on each `tsupport`)
and integrability of `f g`, `f' g` and `f g'`.

This file records the directional corollaries
`∫ (∂ᵢ f) g = -∫ f (∂ᵢ g)` (scalars) and
`∫ ⟨∂ᵢ F, G⟩ = -∫ ⟨F, ∂ᵢ G⟩` (vector fields) used by the Kato–Ponce
commutator and by the vanishing-flux discharge of `H3IBPVanishingFlux`.

Nothing in this file is a `sorry`, a custom axiom, or an `opaque` trick.
-/

open MeasureTheory
open NavierStokes3D (T3)
open scoped InnerProductSpace

set_option autoImplicit false

noncomputable section
namespace IBPWholeSpace

/-- The standard basis vector `eᵢ` on ℝ³. -/
def e (i : Fin 3) : T3 := EuclideanSpace.single i (1 : ℝ)

/-- **Scalar IBP on ℝ³.** If `f, g : ℝ³ → ℝ` are differentiable and the
products `f g`, `(∂ᵢ f) g` and `f (∂ᵢ g)` are integrable, then
`∫ (∂ᵢ f) g = -∫ f (∂ᵢ g)`. -/
theorem integral_partial_mul {f g : T3 → ℝ} (i : Fin 3)
    (hf'g : Integrable (fun x => fderiv ℝ f x (e i) * g x) volume)
    (hfg' : Integrable (fun x => f x * fderiv ℝ g x (e i)) volume)
    (hfg : Integrable (fun x => f x * g x) volume)
    (hf : ∀ x, DifferentiableAt ℝ f x)
    (hg : ∀ x, DifferentiableAt ℝ g x) :
    ∫ x, fderiv ℝ f x (e i) * g x ∂volume =
      -∫ x, f x * fderiv ℝ g x (e i) ∂volume := by
  have h :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (𝕜 := ℝ)
      (v := e i) hf'g hfg' hfg (fun x _ => hf x) (fun x _ => hg x)
  -- Mathlib's form is `∫ f (∂ᵢ g) = -∫ (∂ᵢ f) g`.
  exact (neg_eq_iff_eq_neg.mp h.symm)

/-- Convenience wrapper: the same identity under a global `C¹` assumption. -/
theorem integral_partial_mul_of_contDiff {f g : T3 → ℝ} (i : Fin 3)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hf'g : Integrable (fun x => fderiv ℝ f x (e i) * g x) volume)
    (hfg' : Integrable (fun x => f x * fderiv ℝ g x (e i)) volume)
    (hfg : Integrable (fun x => f x * g x) volume) :
    ∫ x, fderiv ℝ f x (e i) * g x ∂volume =
      -∫ x, f x * fderiv ℝ g x (e i) ∂volume :=
  integral_partial_mul i hf'g hfg' hfg hf.differentiable_one hg.differentiable_one

/-- **Vector IBP on ℝ³.** If `F, G : ℝ³ → ℝ³` are differentiable and the
products `⟨F, G⟩`, `⟨∂ᵢ F, G⟩` and `⟨F, ∂ᵢ G⟩` are integrable, then
`∫ ⟨∂ᵢ F, G⟩ = -∫ ⟨F, ∂ᵢ G⟩`. -/
theorem integral_partial_inner {F G : T3 → T3} (i : Fin 3)
    (hf'g : Integrable (fun x => inner ℝ (fderiv ℝ F x (e i)) (G x)) volume)
    (hfg' : Integrable (fun x => inner ℝ (F x) (fderiv ℝ G x (e i))) volume)
    (hfg : Integrable (fun x => inner ℝ (F x) (G x)) volume)
    (hf : ∀ x, DifferentiableAt ℝ F x)
    (hg : ∀ x, DifferentiableAt ℝ G x) :
    ∫ x, inner ℝ (fderiv ℝ F x (e i)) (G x) ∂volume =
      -∫ x, inner ℝ (F x) (fderiv ℝ G x (e i)) ∂volume := by
  have h :=
    integral_bilinear_fderiv_right_eq_neg_left_of_integrable
      (μ := volume) (B := innerSL ℝ) (v := e i)
      hf'g hfg' hfg (fun x _ => hf x) (fun x _ => hg x)
  exact (neg_eq_iff_eq_neg.mp h.symm)

/-- Convenience wrapper: the same identity under a global `C¹` assumption. -/
theorem integral_partial_inner_of_contDiff {F G : T3 → T3} (i : Fin 3)
    (hf : ContDiff ℝ 1 F) (hg : ContDiff ℝ 1 G)
    (hf'g : Integrable (fun x => inner ℝ (fderiv ℝ F x (e i)) (G x)) volume)
    (hfg' : Integrable (fun x => inner ℝ (F x) (fderiv ℝ G x (e i))) volume)
    (hfg : Integrable (fun x => inner ℝ (F x) (G x)) volume) :
    ∫ x, inner ℝ (fderiv ℝ F x (e i)) (G x) ∂volume =
      -∫ x, inner ℝ (F x) (fderiv ℝ G x (e i)) ∂volume :=
  integral_partial_inner i hf'g hfg' hfg hf.differentiable_one hg.differentiable_one

#print axioms IBPWholeSpace.integral_partial_mul
#print axioms IBPWholeSpace.integral_partial_inner

end IBPWholeSpace
