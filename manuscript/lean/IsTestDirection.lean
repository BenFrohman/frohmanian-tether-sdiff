/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ArnoldGeometric.lean, line 309

/-!
# manuscript.lean.IsTestDirection

Machine-checked Lean 4 module.
-/

@[expose] public def IsTestDirection (ε : CoadjointOrbit) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) ε.val ∧ HasCompactSupport ε.val
