/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 377

/-!
# manuscript.lean.abcProfile

Machine-checked Lean 4 module.
-/

@[expose] public def abcProfile (k A B C : ℝ) : VelocityField :=
  trigField k (abcα A B C) (abcβ A B C) abcj abcl
