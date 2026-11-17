/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 381

/-!
# manuscript.lean.abcFlow

Machine-checked Lean 4 module.
-/

@[expose] public def abcFlow (ν k A B C : ℝ) : TimeDependentVelocity :=
  flow ν k (abcα A B C) (abcβ A B C) abcj abcl
