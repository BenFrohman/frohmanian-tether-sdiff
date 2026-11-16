/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ForMathlib/Projection.lean, line 35

/-!
# manuscript.lean.Pi_u

Machine-checked Lean 4 module.
-/

@[expose] public noncomputable def Pi_u (u v : VelocityField) : VelocityField :=
  fun x => v x - (
    (∫ y, pairing (v y) (u y) ∂volume) /
    (∫ y, ‖u y‖ ^ 2 ∂volume)
  ) • u x
