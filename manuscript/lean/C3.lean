/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/SymplecticTether.lean, line 238

/-!
# manuscript.lean.C3

Machine-checked Lean 4 module.
-/

@[expose] public def ProducesControllableNegativeFeedback
    (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  ∀ (F : Functional) (ω : CoadjointOrbit),
    B ω F F ≤
      -kappa * Enstrophy ω * ∫ x,
          ‖Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x‖ ^ 2
        ∂volume
