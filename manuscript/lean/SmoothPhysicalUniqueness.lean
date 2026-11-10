-- FrohmanianTether/TetheredLyapunov.lean, line 1549
@[expose] public def SmoothPhysicalUniqueness (u₀ : VelocityField) (ν : ℝ) : Prop :=
  ∀ (T : ℝ) (u v : TimeDependentVelocity) (p q : TimeDependentPressure),
    IsLocalPhysicalSolution ν T u₀ u p → IsLocalPhysicalSolution ν T u₀ v q →
      ∀ t ∈ Set.Icc (0 : ℝ) T, u t = v t
