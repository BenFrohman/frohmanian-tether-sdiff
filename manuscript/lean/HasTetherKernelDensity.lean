/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/Uniqueness.lean, line 47

/-!
# manuscript.lean.HasTetherKernelDensity

Machine-checked Lean 4 module.
-/

@[expose] public def HasTetherKernelDensity
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (α : CoadjointOrbit → T3 → ℝ) : Prop :=
  ∀ (ω : CoadjointOrbit) (F G : Functional),
    B ω F G =
      ∫ x,
        α ω x *
          inner ℝ
            (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x)
            (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative G ω) x)
        ∂volume
