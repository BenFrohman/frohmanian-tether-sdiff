/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 836

/-!
# manuscript.lean.abcFlow_isPeriodicSmoothSolutionOn

Machine-checked Lean 4 module.
-/

public theorem abcFlow_isPeriodicSmoothSolutionOn (ν T : ℝ) (m : ℤ) (A B C : ℝ) :
    FrohmanianTether.ClayStatements.IsPeriodicSmoothSolutionOn ν T
      (abcProfile (2 * Real.pi * m) A B C) (abcFlow ν (2 * Real.pi * m) A B C)
      (abcPressure ν (2 * Real.pi * m) A B C) := ...
