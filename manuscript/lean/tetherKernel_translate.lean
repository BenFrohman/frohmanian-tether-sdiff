/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherEquivariantC1.lean, line 259

/-!
# manuscript.lean.tetherKernel_translate

Machine-checked Lean 4 module.
-/

public theorem tetherKernel_translate (h : T3) (F G : Functional) (ω : CoadjointOrbit) :
    TetherKernel (translate h • ω) (fun η => F ((translate h)⁻¹ • η))
      (fun η => G ((translate h)⁻¹ • η)) = TetherKernel ω F G := ...
