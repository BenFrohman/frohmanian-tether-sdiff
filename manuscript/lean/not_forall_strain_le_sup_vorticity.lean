/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/StrainBoundRefutation.lean, line 78

/-!
# manuscript.lean.not_forall_strain_le_sup_vorticity

Machine-checked Lean 4 module.
-/

public theorem not_forall_strain_le_sup_vorticity (C : ℝ) :
    ¬ ∀ (u : VelocityField) (x : T3),
      ‖fderiv ℝ u x‖ ≤ C * vorticity_sup_norm (curl u) := ...
