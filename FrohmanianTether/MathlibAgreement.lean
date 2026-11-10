/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import FrohmanianTether.TetherEquivariantC1

/-!
# Project-local names that agree with Mathlib declarations

Short local names used in the library, each proved equal to the Mathlib declaration it
abbreviates (all by `rfl`). Concepts Mathlib lacks (curl, divergence-free fields `DivFreeL2`,
the test directions, `Pi_u`, the Biot–Savart integral) remain project-local.
-/

open MeasureTheory NavierStokes3D ArnoldGeometric TetherNondegeneracy TestFieldFamily
open scoped InnerProductSpace

noncomputable section

namespace MathlibAgreement

/-- `NavierStokes3D.volume` is Mathlib's Lebesgue (Haar) measure `MeasureTheory.volume`. -/
public theorem volume_eq : (NavierStokes3D.volume : Measure T3) = MeasureTheory.volume := rfl

/-- `pairing` is Mathlib's real inner product. -/
public theorem pairing_eq_inner (u v : EuclideanSpace ℝ (Fin 3)) : pairing u v = ⟪u, v⟫_ℝ := rfl

/-- `eb i` is Mathlib's `EuclideanSpace.single i 1`. -/
public theorem eb_eq_single (i : Fin 3) : eb i = EuclideanSpace.single i (1 : ℝ) := rfl

/-- `pd H i y` is Mathlib's `fderiv ℝ H y` applied to the `i`-th basis vector. -/
public theorem pd_eq_fderiv (H : T3 → ℝ) (i : Fin 3) (y : T3) :
    pd H i y = fderiv ℝ H y (EuclideanSpace.single i 1) := rfl

/-- `NavierStokes3D.div` is the sum of Mathlib `fderiv` partials along the standard basis. -/
public theorem div_eq_sum_fderiv (u : T3 → EuclideanSpace ℝ (Fin 3)) (x : T3) :
    NavierStokes3D.div u x = ∑ i : Fin 3, fderiv ℝ (fun y => u y i) x (EuclideanSpace.single i 1) :=
  rfl

/-- `cross` is Mathlib's `crossProduct` transported to `EuclideanSpace`. -/
public theorem cross_eq_crossProduct (u v : EuclideanSpace ℝ (Fin 3)) :
    cross u v = WithLp.toLp 2 (crossProduct (WithLp.ofLp u) (WithLp.ofLp v)) := rfl

/-- `ConcreteSDiff.translate h` is Mathlib's `Equiv.addRight h`. -/
public theorem translate_eq_addRight (h : T3) :
    ((ConcreteSDiff.translate h : ConcreteSDiff.G) : Equiv.Perm T3) = Equiv.addRight h := rfl

/-- `l2Translate h` is Mathlib's `Lp.compMeasurePreservingₗᵢ` along `x ↦ x - h`. -/
public theorem l2Translate_eq (h : T3) :
    TetherEquivariant.l2Translate h =
      Lp.compMeasurePreservingₗᵢ ℝ (fun x : T3 => x - h) (TetherEquivariant.mp_sub h) := rfl

/-- `Enstrophy` is the Lebesgue integral of `‖ω‖²`. -/
public theorem enstrophy_eq (ω : CoadjointOrbit) :
    Enstrophy ω = ∫ x, ‖ω.val x‖ ^ 2 ∂MeasureTheory.volume := rfl

end MathlibAgreement

end
