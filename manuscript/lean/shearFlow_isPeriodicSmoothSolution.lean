-- FrohmanianTether/ExplicitFlows.lean, line 557
public theorem shearFlow_isPeriodicSmoothSolution (ν : ℝ) (m : ℤ) (a : ℝ) :
    FrohmanianTether.ClayStatements.IsPeriodicSmoothSolution ν
      (shearProfile (2 * Real.pi * m) a) (fun _ _ => 0)
      (shearFlow ν (2 * Real.pi * m) a) shearPressure := ...
