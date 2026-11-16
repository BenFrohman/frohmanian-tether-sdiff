/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 830

/-!
# manuscript.lean.shearFlow_isPeriodicSmoothSolutionOn

Machine-checked Lean 4 module.
-/

public theorem shearFlow_isPeriodicSmoothSolutionOn (ν T : ℝ) (m : ℤ) (a : ℝ) :
    FrohmanianTether.ClayStatements.IsPeriodicSmoothSolutionOn ν T
      (shearProfile (2 * Real.pi * m) a) (shearFlow ν (2 * Real.pi * m) a) shearPressure := ...
