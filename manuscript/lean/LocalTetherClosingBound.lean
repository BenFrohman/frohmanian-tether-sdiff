-- FrohmanianTether/ClayStatements.lean, line 57
@[expose] public def LocalTetherClosingBound (ν : ℝ) : Prop :=
  ∀ u₀ : VelocityField,
    (∀ x, div u₀ x = 0) → ContDiff ℝ (⊤ : ℕ∞) u₀ →
      Integrable (fun x : T3 => ‖u₀ x‖ ^ 2) →
        TetheredLyapunov.LocalTetherBound u₀ ν
