/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherEquivariantC1.lean, line 155

/-!
# manuscript.lean.isFunctionalGradient_translate

Machine-checked Lean 4 module.
-/

public theorem isFunctionalGradient_translate (h : T3) {F : CoadjointOrbit → ℝ}
    {ω : CoadjointOrbit} {g : L2Field} (hg : IsFunctionalGradient F ω g) :
    IsFunctionalGradient (fun η => F ((translate h)⁻¹ • η)) (translate h • ω)
      (l2Translate h g) := ...
