@[expose] public def Clay_A_Fefferman : Prop :=
  ∀ (ν : ℝ) (u₀ : VelocityField),
    0 < ν → ContDiff ℝ ∞ u₀ → (∀ x, div u₀ x = 0) → FeffermanDecay u₀ →
      ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
        FeffermanGlobalSolution ν u₀ u p
