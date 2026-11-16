/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherDefinitionAudit.lean, line 200

/-!
# manuscript.lean.vorticity_sup_norm_escapePath_pos

Machine-checked Lean 4 module.
-/

public theorem vorticity_sup_norm_escapePath_pos {t : ℝ} (ht : 0 < t) :
    vorticity_sup_norm (vorticity (escapePath t)) = t⁻¹ := ...
