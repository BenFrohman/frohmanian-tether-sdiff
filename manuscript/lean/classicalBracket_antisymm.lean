/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ArnoldGeometric.lean, line 1211

/-!
# manuscript.lean.classicalBracket_antisymm

Machine-checked Lean 4 module.
-/

public theorem classicalBracket_antisymm (F G : CoadjointOrbit → ℝ) (ω : CoadjointOrbit) :
    ClassicalBracket F G ω = - ClassicalBracket G F ω := ...
