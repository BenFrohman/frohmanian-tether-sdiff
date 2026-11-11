-- FrohmanianTether/TetherImpliesBKM.lean, line 61
public theorem periodicTetherClosingBound_iff (ν : ℝ) :
    PeriodicTetherClosingBound ν ↔
      ∀ u₀ : VelocityField, (∀ x, div u₀ x = 0) → ContDiff ℝ (⊤ : ℕ∞) u₀ → IsZ3Periodic u₀ →
        PeriodicTetherBound ν u₀ := ...
