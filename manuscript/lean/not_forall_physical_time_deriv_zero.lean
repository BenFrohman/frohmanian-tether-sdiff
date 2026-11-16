/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/PhysicalSolutionSanity.lean, line 157

/-!
# manuscript.lean.not_forall_physical_time_deriv_zero

Machine-checked Lean 4 module.
-/

public theorem not_forall_physical_time_deriv_zero :
    ¬ ∀ u : TimeDependentVelocity, IsPhysicalNSSolution u →
      ∀ x : T3, deriv (fun s => u s x) 0 = 0 := ...
