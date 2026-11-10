-- FrohmanianTether/NS_Equations.lean, line 2329
@[expose] public def IsLocalPhysicalSolution (ν T : ℝ) (u₀ : VelocityField)
    (u : TimeDependentVelocity) (p : TimeDependentPressure) : Prop :=
  u 0 = u₀ ∧ NS_PDE_On u p ν T ∧ (∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (⊤ : ℕ∞) (u t)) ∧
    IsPhysicalNSSolutionOn u T
