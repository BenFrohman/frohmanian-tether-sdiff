/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
module

public import FrohmanianTether.ArnoldGeometric
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.GroupTheory.Perm.Basic

/-!
# A concrete measure-preserving group acting on `CoadjointOrbit`

`ConcreteSDiff` is a `Subgroup (Equiv.Perm T3)`: bijections `g` with `g`, `g⁻¹` measurable and
`MeasureTheory.MeasurePreserving` for `volume`, and which preserve divergence-freeness of
`ω ∘ g⁻¹` (both directions). The action is **scalar composition** `g • ω = ω ∘ g⁻¹`.

Scope (honest): `T3` here is `EuclideanSpace ℝ (Fin 3)` (not the quotient torus); no smoothness
is imposed; the action is NOT the geometric pushforward `(Dg · ω) ∘ g⁻¹`; divergence
preservation is part of the subgroup's defining predicate, not a theorem. `casimir_invariant`
is PROVED (`MeasurePreserving.integral_comp'`), so `SDiffActionHyp` holds for this action
(`sdiffActionHyp`). The former field `transitive_on_casimir_levels` is REFUTED for this action
(`not_transitive_on_casimir_levels`) and was removed from `SDiffActionHyp`.
-/

@[expose] public section

namespace ConcreteSDiff

open ArnoldGeometric NavierStokes3D MeasureTheory

/-- Divergence-preservation predicate for composition with `h`. -/
def DivPres (h : T3 → T3) : Prop :=
  ∀ ω : CoadjointOrbit, ∀ x, NavierStokes3D.div (ω.val ∘ h) x = 0

/-- Defining predicate of the concrete group. -/
def Good (g : Equiv.Perm T3) : Prop :=
  Measurable g ∧ Measurable (g⁻¹ : Equiv.Perm T3) ∧
    MeasurePreserving g MeasureTheory.volume MeasureTheory.volume ∧ MeasurePreserving (g⁻¹ : Equiv.Perm T3) MeasureTheory.volume MeasureTheory.volume ∧
    DivPres g ∧ DivPres (g⁻¹ : Equiv.Perm T3)

theorem coe_mul (g h : Equiv.Perm T3) : ((g * h : Equiv.Perm T3) : T3 → T3) = g ∘ h := rfl

theorem divPres_comp {a b : T3 → T3} (ha : DivPres a) (hb : DivPres b) : DivPres (a ∘ b) :=
  fun ω x => by
    have := hb ⟨ω.val ∘ a, ha ω⟩ x
    simpa [Function.comp_assoc] using this

/-- The concrete subgroup of `Equiv.Perm T3`. -/
def SDiffConcrete : Subgroup (Equiv.Perm T3) where
  carrier := {g | Good g}
  one_mem' := by
    refine ⟨measurable_id, measurable_id, MeasurePreserving.id _, MeasurePreserving.id _, ?_, ?_⟩ <;>
      exact fun ω x => by simpa using ω.property x
  mul_mem' := by
    rintro g h ⟨g1, g2, g3, g4, g5, g6⟩ ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨g1.comp h1, ?_, g3.comp h3, ?_, (show DivPres (g ∘ h) from divPres_comp g5 h5), ?_⟩
    · rw [mul_inv_rev]; exact h2.comp g2
    · rw [mul_inv_rev]; exact h4.comp g4
    · rw [mul_inv_rev]; exact (show DivPres (((h⁻¹ : Equiv.Perm T3) : T3 → T3) ∘ ((g⁻¹ : Equiv.Perm T3) : T3 → T3)) from divPres_comp h6 g6)
  inv_mem' := by
    rintro g ⟨g1, g2, g3, g4, g5, g6⟩
    exact ⟨g2, by simpa using g1, g4, by simpa using g3, g6, by simpa using g5⟩

abbrev G : Type := SDiffConcrete

theorem good (g : G) : Good (g : Equiv.Perm T3) := g.2

/-- Concrete action: `g • ω = ω ∘ g⁻¹`. -/
noncomputable instance : MulAction G CoadjointOrbit where
  smul g ω := ⟨ω.val ∘ ((g⁻¹ : G) : Equiv.Perm T3), (good g⁻¹).2.2.2.2.1 ω⟩
  one_smul ω := by cases ω; rfl
  mul_smul g h ω := by cases ω; rfl

theorem smul_val (g : G) (ω : CoadjointOrbit) :
    (g • ω).val = ω.val ∘ ((g⁻¹ : G) : Equiv.Perm T3) := rfl

/-- The pushforward as a Mathlib `MeasurableEquiv`. -/
noncomputable def toMeasurableEquiv (g : G) : T3 ≃ᵐ T3 where
  toEquiv := (g : Equiv.Perm T3)
  measurable_toFun := (good g).1
  measurable_invFun := (good g).2.1

/-- **Proved** `casimir_invariant` for the concrete action. -/
theorem casimir_invariant (f : ℝ → ℝ) (g : G) (ω : CoadjointOrbit) :
    (∫ x, f ‖(g • ω).val x‖ ∂volume) = ∫ x, f ‖ω.val x‖ ∂volume := by
  have hmp : MeasurePreserving (toMeasurableEquiv g⁻¹) MeasureTheory.volume MeasureTheory.volume := (good g⁻¹).2.2.1
  rw [smul_val]
  exact hmp.integral_comp' (fun y => f ‖ω.val y‖)

/-- Enstrophy invariance, proved. -/
theorem enstrophy_invariant (g : G) (ω : CoadjointOrbit) :
    Enstrophy (g • ω) = Enstrophy ω := casimir_invariant (fun r => r ^ 2) g ω

/-- **Proved.** `SDiffActionHyp` holds for the concrete group (no open field remains). -/
theorem sdiffActionHyp : SDiffActionHyp G :=
  ⟨casimir_invariant⟩

/-- A constant vector field, as a (divergence-free) element of `CoadjointOrbit`. -/
noncomputable def constOrbit (c : EuclideanSpace ℝ (Fin 3)) : CoadjointOrbit :=
  ⟨fun _ => c, fun x => by simp [NavierStokes3D.div]⟩

theorem smul_constOrbit (g : G) (c : EuclideanSpace ℝ (Fin 3)) :
    g • constOrbit c = constOrbit c := rfl

/-- **Refutation of the removed hypothesis `transitive_on_casimir_levels`** for the concrete
action. The constant fields `e₀` and `e₁` have pointwise norm `1`, hence the same Casimir
`∫ f(|ω|)` for every `f`, but the action (composition with a bijection) fixes every constant
field, so no group element maps `e₀` to `e₁`. -/
theorem not_transitive_on_casimir_levels :
    ¬ ∀ ω₁ ω₂ : CoadjointOrbit,
      (∀ f : ℝ → ℝ, Casimir f ω₁ = Casimir f ω₂) → ∃ g : G, g • ω₁ = ω₂ := by
  intro h
  set e0 : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 1
  set e1 : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 1 1
  have hcas : ∀ f : ℝ → ℝ, Casimir f (constOrbit e0) = Casimir f (constOrbit e1) := by
    intro f
    simp [Casimir, constOrbit, e0, e1]
  obtain ⟨g, hg⟩ := h _ _ hcas
  rw [smul_constOrbit] at hg
  have h1 := congrArg (fun ω : CoadjointOrbit => ω.val 0 0) hg
  simp [constOrbit, e0, e1] at h1

end ConcreteSDiff

end

#print axioms ConcreteSDiff.casimir_invariant
#print axioms ConcreteSDiff.enstrophy_invariant
#print axioms ConcreteSDiff.sdiffActionHyp
#print axioms ConcreteSDiff.not_transitive_on_casimir_levels
