/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 393

/-!
# manuscript.lean.abcPressure0

Machine-checked Lean 4 module.
-/

@[expose] public def abcPressure₀ (k A B C : ℝ) : PressureField := fun y =>
  -((abcProfile k A B C y 0) ^ 2 + (abcProfile k A B C y 1) ^ 2 +
    (abcProfile k A B C y 2) ^ 2) / 2
