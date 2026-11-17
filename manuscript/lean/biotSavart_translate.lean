/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherEquivariantC1.lean, line 211

/-!
# manuscript.lean.biotSavart_translate

Machine-checked Lean 4 module.
-/

public theorem biotSavart_translate (h : T3) (ω : CoadjointOrbit) :
    velocity_from_vorticity (translate h • ω) = fun x => velocity_from_vorticity ω (x - h) := ...
