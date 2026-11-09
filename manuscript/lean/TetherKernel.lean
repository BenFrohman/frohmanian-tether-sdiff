/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
@[expose] public noncomputable def TetherKernel (ω : CoadjointOrbit) (F G : Functional) : ℝ :=
  -kappa * Enstrophy ω * ∫ x,
      inner ℝ
        (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x)
        (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative G ω) x)
    ∂volume
