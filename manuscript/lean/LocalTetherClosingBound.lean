-- FrohmanianTether/ClayStatements.lean, line 61
@[expose] public def LocalTetherClosingBound (ν : ℝ) : Prop :=
  ∀ u₀ : VelocityField,
    (∀ x, div u₀ x = 0) → ContDiff ℝ (⊤ : ℕ∞) u₀ →
      Integrable (fun x : T3 => ‖u₀ x‖ ^ 2) →
        BddAbove (Set.range fun x => ‖vorticity u₀ x‖) →
          TetheredLyapunov.LocalTetherBound u₀ ν
