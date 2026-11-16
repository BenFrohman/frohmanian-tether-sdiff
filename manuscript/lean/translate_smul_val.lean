/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherEquivariantC1.lean, line 70

/-!
# manuscript.lean.translate_smul_val

Machine-checked Lean 4 module.
-/

public theorem translate_smul_val (h : T3) (ω : CoadjointOrbit) :
    (translate h • ω).val = fun y => ω.val (y - h) := ...
