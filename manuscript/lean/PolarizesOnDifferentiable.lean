/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/Uniqueness.lean, line 241

/-!
# manuscript.lean.PolarizesOnDifferentiable

Machine-checked Lean 4 module.
-/

@[expose] public def PolarizesOnDifferentiable
    (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  ∀ (ω : CoadjointOrbit) (F G : Functional),
    (∃ g, IsFunctionalGradient F ω g) → (∃ g, IsFunctionalGradient G ω g) →
    2 * B ω F G =
      B ω (fun ω' => F ω' + G ω') (fun ω' => F ω' + G ω') - B ω F F - B ω G G
