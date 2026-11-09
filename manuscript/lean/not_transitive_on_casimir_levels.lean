-- FrohmanianTether/ConcreteSDiff.lean, line 112
theorem not_transitive_on_casimir_levels :
    ¬ ∀ ω₁ ω₂ : CoadjointOrbit,
      (∀ f : ℝ → ℝ, Casimir f ω₁ = Casimir f ω₂) → ∃ g : G, g • ω₁ = ω₂ := ...
