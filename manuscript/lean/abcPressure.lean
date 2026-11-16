/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 403

/-!
# manuscript.lean.abcPressure

Machine-checked Lean 4 module.
-/

@[expose] public def abcPressure (ν k A B C : ℝ) : TimeDependentPressure :=
  flowPressure ν k (abcPressure₀ k A B C)
