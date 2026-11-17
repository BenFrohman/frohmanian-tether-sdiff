@[expose] public def R3BKMContinuation (ν : ℝ) : Prop :=
  ∀ u₀ : VelocityField, ContDiff ℝ ∞ u₀ → (∀ x, div u₀ x = 0) → FeffermanDecay u₀ →
    R3BKMContinuationAt ν u₀
