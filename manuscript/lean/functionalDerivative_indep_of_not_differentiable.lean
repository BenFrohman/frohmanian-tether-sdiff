/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ArnoldGeometric.lean, line 407

/-!
# manuscript.lean.functionalDerivative_indep_of_not_differentiable

Machine-checked Lean 4 module.
-/

public theorem functionalDerivative_indep_of_not_differentiable
    {ω : CoadjointOrbit} (hω : ¬ ∀ i x, DifferentiableAt ℝ (fun y => ω.val y i) x)
    (F G : CoadjointOrbit → ℝ) :
    FunctionalDerivative F ω = FunctionalDerivative G ω := ...
