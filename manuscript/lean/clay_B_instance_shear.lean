/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 806

/-!
# manuscript.lean.clay_B_instance_shear

Machine-checked Lean 4 module.
-/

public theorem clay_B_instance_shear (ν : ℝ) (m : ℤ) (a : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (shearProfile (2 * Real.pi * m) a) ∧
    (∀ x, div (shearProfile (2 * Real.pi * m) a) x = 0) ∧
    FrohmanianTether.ClayStatements.IsZ3Periodic (shearProfile (2 * Real.pi * m) a) ∧
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      FrohmanianTether.ClayStatements.IsPeriodicSmoothSolution ν
        (shearProfile (2 * Real.pi * m) a) (fun _ _ => 0) u p := ...
