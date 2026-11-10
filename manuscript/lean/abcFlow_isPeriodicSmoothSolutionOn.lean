-- FrohmanianTether/ExplicitFlows.lean, line 836
public theorem abcFlow_isPeriodicSmoothSolutionOn (ν T : ℝ) (m : ℤ) (A B C : ℝ) :
    FrohmanianTether.ClayStatements.IsPeriodicSmoothSolutionOn ν T
      (abcProfile (2 * Real.pi * m) A B C) (abcFlow ν (2 * Real.pi * m) A B C)
      (abcPressure ν (2 * Real.pi * m) A B C) := ...
