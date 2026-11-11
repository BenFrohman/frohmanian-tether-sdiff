-- FrohmanianTether/TetherImpliesBKM.lean, line 45
@[expose] public def PeriodicTetherBound (ν : ℝ) (u₀ : VelocityField) : Prop :=
  ∃ Y : ℝ, ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
    IsPeriodicSmoothSolutionOn ν T u₀ u p →
      ∀ t ∈ Set.Ico (0 : ℝ) T, vorticity_sup_norm (vorticity (u t)) ≤ Y
