/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/SymplecticTether.lean, line 198

/-!
# manuscript.lean.TetherKernel

Machine-checked Lean 4 module.
-/

@[expose] public noncomputable def TetherKernel (ω : CoadjointOrbit) (F G : Functional) : ℝ :=
  -kappa * Enstrophy ω * ∫ x,
      inner ℝ
        (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x)
        (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative G ω) x)
    ∂volume
