/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/SymplecticConstraint.lean, line 718

/-!
# manuscript.lean.nonzero_smooth_ns_solution_exists

Machine-checked Lean 4 module.
-/

public theorem nonzero_smooth_ns_solution_exists (ν : ℝ) (c : T3) (hc : c ≠ 0) :
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      u 0 ≠ 0 ∧
      (∀ t ≥ (0 : ℝ), IsSmooth (u t)) ∧
      navier_stokes_eq u p ν := ...
