/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 557

/-!
# manuscript.lean.shearFlow_isPeriodicSmoothSolution

Machine-checked Lean 4 module.
-/

public theorem shearFlow_isPeriodicSmoothSolution (ν : ℝ) (m : ℤ) (a : ℝ) :
    FrohmanianTether.ClayStatements.IsPeriodicSmoothSolution ν
      (shearProfile (2 * Real.pi * m) a) (fun _ _ => 0)
      (shearFlow ν (2 * Real.pi * m) a) shearPressure := ...
