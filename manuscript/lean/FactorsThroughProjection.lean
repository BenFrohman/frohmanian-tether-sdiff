/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/Uniqueness.lean, line 399

/-!
# manuscript.lean.FactorsThroughProjection

Machine-checked Lean 4 module.
-/

@[expose] public def FactorsThroughProjection
    (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  ∀ ω : CoadjointOrbit, ∃ Q : (T3 → EuclideanSpace ℝ (Fin 3)) → (T3 → EuclideanSpace ℝ (Fin 3)) → ℝ,
    (∀ a b, Q a b = Q b a) ∧
    ∀ F G : Functional, B ω F G =
      Q (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω))
        (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative G ω))
