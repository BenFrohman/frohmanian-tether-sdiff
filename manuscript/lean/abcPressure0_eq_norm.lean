/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 397

/-!
# manuscript.lean.abcPressure0_eq_norm

Machine-checked Lean 4 module.
-/

public theorem abcPressure₀_eq_norm (k A B C : ℝ) (y : T3) :
    abcPressure₀ k A B C y = -‖abcProfile k A B C y‖ ^ 2 / 2 := ...
