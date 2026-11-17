/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 437

/-!
# manuscript.lean.abc_balance

Machine-checked Lean 4 module.
-/

public theorem abc_balance (k A B C : ℝ) (x : T3) :
    convective (abcProfile k A B C) (abcProfile k A B C) x +
      pressureGradient (abcPressure₀ k A B C) x = 0 := ...
