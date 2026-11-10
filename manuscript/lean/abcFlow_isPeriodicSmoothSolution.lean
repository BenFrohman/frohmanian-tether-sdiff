-- FrohmanianTether/ExplicitFlows.lean, line 585
public theorem abcFlow_isPeriodicSmoothSolution (ν : ℝ) (m : ℤ) (A B C : ℝ) :
    FrohmanianTether.ClayStatements.IsPeriodicSmoothSolution ν
      (abcProfile (2 * Real.pi * m) A B C) (fun _ _ => 0)
      (abcFlow ν (2 * Real.pi * m) A B C) (abcPressure ν (2 * Real.pi * m) A B C) := ...
