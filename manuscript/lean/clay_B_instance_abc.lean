/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 818

/-!
# manuscript.lean.clay_B_instance_abc

Machine-checked Lean 4 module.
-/

public theorem clay_B_instance_abc (ν : ℝ) (m : ℤ) (A B C : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (abcProfile (2 * Real.pi * m) A B C) ∧
    (∀ x, div (abcProfile (2 * Real.pi * m) A B C) x = 0) ∧
    FrohmanianTether.ClayStatements.IsZ3Periodic (abcProfile (2 * Real.pi * m) A B C) ∧
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      FrohmanianTether.ClayStatements.IsPeriodicSmoothSolution ν
        (abcProfile (2 * Real.pi * m) A B C) (fun _ _ => 0) u p := ...
