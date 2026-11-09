/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
-- NS_Millennium_Proof/Modules/ArnoldGeometric.lean (abstract SDiff action; replaces the former identity stub)
public abbrev CoadjointAction {SDiff : Type*} [Group SDiff] [MulAction SDiff CoadjointOrbit]
    (g : SDiff) (ω : CoadjointOrbit) : CoadjointOrbit :=
  g • ω

public structure SDiffActionHyp (SDiff : Type*) [Group SDiff] [MulAction SDiff CoadjointOrbit] :
    Prop where
  casimir_invariant : ∀ (f : ℝ → ℝ) (g : SDiff) (ω : CoadjointOrbit),
    (∫ x, f ‖(g • ω).val x‖ ∂volume) = ∫ x, f ‖ω.val x‖ ∂volume
  transitive_on_casimir_levels : ∀ ω₁ ω₂ : CoadjointOrbit,
    (∀ f : ℝ → ℝ, Casimir f ω₁ = Casimir f ω₂) → ∃ g : SDiff, g • ω₁ = ω₂
