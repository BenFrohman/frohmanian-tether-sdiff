/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ArnoldGeometric.lean, line 367

/-!
# manuscript.lean.FunctionalDerivative

Machine-checked Lean 4 module.
-/

@[expose] public noncomputable def FunctionalDerivative (F : CoadjointOrbit → ℝ) (ω : CoadjointOrbit) : T3 → EuclideanSpace ℝ (Fin 3) :=
  if h : ∃ g, IsFunctionalGradient F ω g then ⇑(Classical.choose h) else 0
