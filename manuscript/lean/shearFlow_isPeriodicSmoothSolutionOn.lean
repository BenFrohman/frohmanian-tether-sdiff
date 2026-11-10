-- FrohmanianTether/ExplicitFlows.lean, line 830
public theorem shearFlow_isPeriodicSmoothSolutionOn (ν T : ℝ) (m : ℤ) (a : ℝ) :
    FrohmanianTether.ClayStatements.IsPeriodicSmoothSolutionOn ν T
      (shearProfile (2 * Real.pi * m) a) (shearFlow ν (2 * Real.pi * m) a) shearPressure := ...
