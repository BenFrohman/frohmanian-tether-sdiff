/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/Uniqueness.lean, line 317

/-!
# manuscript.lean.polarizes_tetherKernel_zero_of_not_differentiable

Machine-checked Lean 4 module.
-/

public theorem polarizes_tetherKernel_zero_of_not_differentiable
    (hP : Polarizes TetherKernel)
    {ω : CoadjointOrbit} (hω : ¬ ∀ i x, DifferentiableAt ℝ (fun y => ω.val y i) x)
    (F G : Functional) : TetherKernel ω F G = 0 := ...
