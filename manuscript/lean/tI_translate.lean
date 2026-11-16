/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherEquivariantC1.lean, line 225

/-!
# manuscript.lean.tI_translate

Machine-checked Lean 4 module.
-/

public theorem tI_translate (h : T3) (ω : CoadjointOrbit)
    {a b a' b' : T3 → EuclideanSpace ℝ (Fin 3)}
    (ha : a' =ᵐ[MeasureTheory.volume] fun x => a (x - h))
    (hb : b' =ᵐ[MeasureTheory.volume] fun x => b (x - h)) :
    tI (translate h • ω) a' b' = tI ω a b := ...
