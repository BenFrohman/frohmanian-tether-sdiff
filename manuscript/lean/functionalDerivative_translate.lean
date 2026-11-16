/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherEquivariantC1.lean, line 181

/-!
# manuscript.lean.functionalDerivative_translate

Machine-checked Lean 4 module.
-/

public theorem functionalDerivative_translate (h : T3) (F : CoadjointOrbit → ℝ)
    (ω : CoadjointOrbit) :
    FunctionalDerivative (fun η => F ((translate h)⁻¹ • η)) (translate h • ω)
      =ᵐ[MeasureTheory.volume] fun x => FunctionalDerivative F ω (x - h) := ...
