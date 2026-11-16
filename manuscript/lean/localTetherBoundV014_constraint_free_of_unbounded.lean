/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherDefinitionAudit.lean, line 61

/-!
# manuscript.lean.localTetherBoundV014_constraint_free_of_unbounded

Machine-checked Lean 4 module.
-/

public theorem localTetherBoundV014_constraint_free_of_unbounded {u : TimeDependentVelocity}
    {t Y : ℝ} (hY : 0 ≤ Y) (h : ¬ BddAbove (Set.range fun x => ‖vorticity (u t) x‖)) :
    vorticity_sup_norm (vorticity (u t)) ≤ Y := ...
