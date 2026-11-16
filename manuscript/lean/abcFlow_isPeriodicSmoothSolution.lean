/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 585

/-!
# manuscript.lean.abcFlow_isPeriodicSmoothSolution

Machine-checked Lean 4 module.
-/

public theorem abcFlow_isPeriodicSmoothSolution (ν : ℝ) (m : ℤ) (A B C : ℝ) :
    FrohmanianTether.ClayStatements.IsPeriodicSmoothSolution ν
      (abcProfile (2 * Real.pi * m) A B C) (fun _ _ => 0)
      (abcFlow ν (2 * Real.pi * m) A B C) (abcPressure ν (2 * Real.pi * m) A B C) := ...
