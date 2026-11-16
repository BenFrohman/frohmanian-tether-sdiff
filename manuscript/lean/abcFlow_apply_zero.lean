/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 605

/-!
# manuscript.lean.abcFlow_apply_zero

Machine-checked Lean 4 module.
-/

public theorem abcFlow_apply_zero (ν k A B C : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    abcFlow ν k A B C t 0 = Real.exp (-(ν * k ^ 2) * t) • WithLp.toLp 2 ![C, A, B] := ...
