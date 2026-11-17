/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ArnoldGeometric.lean, line 219

/-!
# manuscript.lean.SDiffActionHyp

Machine-checked Lean 4 module.
-/

public structure SDiffActionHyp (SDiff : Type*) [Group SDiff] [MulAction SDiff CoadjointOrbit] :
    Prop where
  casimir_invariant : ∀ (f : ℝ → ℝ) (g : SDiff) (ω : CoadjointOrbit),
    (∫ x, f ‖(g • ω).val x‖ ∂volume) = ∫ x, f ‖ω.val x‖ ∂volume
