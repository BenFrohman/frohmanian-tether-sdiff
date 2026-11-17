/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ConcreteSDiff.lean, line 87

/-!
# manuscript.lean.casimir_invariant_concrete

Machine-checked Lean 4 module.
-/

theorem casimir_invariant (f : ℝ → ℝ) (g : G) (ω : CoadjointOrbit) :
    (∫ x, f ‖(g • ω).val x‖ ∂volume) = ∫ x, f ‖ω.val x‖ ∂volume := ...
