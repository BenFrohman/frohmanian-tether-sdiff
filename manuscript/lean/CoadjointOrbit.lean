/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ArnoldGeometric.lean, line 167

/-!
# manuscript.lean.CoadjointOrbit

Machine-checked Lean 4 module.
-/

public structure CoadjointOrbit where
  val : T3 → EuclideanSpace ℝ (Fin 3)
  property : ∀ x, NavierStokes3D.div val x = 0
