-- FrohmanianTether/TetheredLyapunov.lean, line 1459
@[expose] public def LocalTetherBound (u₀ : VelocityField) (ν : ℝ) : Prop :=
  ∃ Y : ℝ, ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
    IsLocalPhysicalSolution ν T u₀ u p →
      ∀ t ∈ Set.Icc (0 : ℝ) T, vorticity_sup_norm (vorticity (u t)) ≤ Y
