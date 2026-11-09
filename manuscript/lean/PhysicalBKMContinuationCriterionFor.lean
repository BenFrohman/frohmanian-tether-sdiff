-- FrohmanianTether/TetheredLyapunov.lean, line 1843
@[expose] public def PhysicalBKMContinuationCriterionFor (u₀ : VelocityField) (ν : ℝ) : Prop :=
  ∀ u : ℝ → VelocityField, ∀ p : ℝ → PressureField,
    NS_PDE u p ν → u 0 = u₀ → IsPhysicalNSSolution u → BKMContinuationCriterion u ν
