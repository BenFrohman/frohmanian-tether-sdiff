/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/PlanSteps.lean, line 61

/-!
# manuscript.lean.IsCoadjointMotion

Machine-checked Lean 4 module.
-/

def IsCoadjointMotion (SDiff : Type*) [Group SDiff] [MulAction SDiff CoadjointOrbit]
    (ω : ℝ → CoadjointOrbit) : Prop :=
  ∃ g : ℝ → SDiff, ∀ t, ω t = g t • ω 0
