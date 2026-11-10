-- FrohmanianTether/ClayStatements.lean, line 48
@[expose] public def FrohmanianTetherClosingBound (ν : ℝ) : Prop :=
  ∀ u₀ : VelocityField,
    (∀ x, div u₀ x = 0) → ContDiff ℝ (⊤ : ℕ∞) u₀ →
      Integrable (fun x : T3 => ‖u₀ x‖ ^ 2) →
        FrohmanianTetherBound u₀ ν
