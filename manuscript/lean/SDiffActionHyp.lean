-- FrohmanianTether/ArnoldGeometric.lean, line 220
public structure SDiffActionHyp (SDiff : Type*) [Group SDiff] [MulAction SDiff CoadjointOrbit] :
    Prop where
  casimir_invariant : ∀ (f : ℝ → ℝ) (g : SDiff) (ω : CoadjointOrbit),
    (∫ x, f ‖(g • ω).val x‖ ∂volume) = ∫ x, f ‖ω.val x‖ ∂volume
  transitive_on_casimir_levels : ∀ ω₁ ω₂ : CoadjointOrbit,
    (∀ f : ℝ → ℝ, Casimir f ω₁ = Casimir f ω₂) → ∃ g : SDiff, g • ω₁ = ω₂
