/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherDefinitionAudit.lean, line 49

/-!
# manuscript.lean.vorticity_sup_norm_eq_zero_of_not_bddAbove

Machine-checked Lean 4 module.
-/

public theorem vorticity_sup_norm_eq_zero_of_not_bddAbove {w : VorticityField}
    (h : ¬ BddAbove (Set.range fun x => ‖w x‖)) : vorticity_sup_norm w = 0 := ...
