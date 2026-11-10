-- FrohmanianTether/ExplicitFlows.lean, line 806
public theorem clay_B_instance_shear (ν : ℝ) (m : ℤ) (a : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (shearProfile (2 * Real.pi * m) a) ∧
    (∀ x, div (shearProfile (2 * Real.pi * m) a) x = 0) ∧
    FrohmanianTether.ClayStatements.IsZ3Periodic (shearProfile (2 * Real.pi * m) a) ∧
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      FrohmanianTether.ClayStatements.IsPeriodicSmoothSolution ν
        (shearProfile (2 * Real.pi * m) a) (fun _ _ => 0) u p := ...
