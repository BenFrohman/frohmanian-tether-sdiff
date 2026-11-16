/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 612

/-!
# manuscript.lean.abcFlow_ne_zero

Machine-checked Lean 4 module.
-/

public theorem abcFlow_ne_zero (ν k : ℝ) {A B C : ℝ} (hABC : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) {t : ℝ}
    (ht : 0 ≤ t) : abcFlow ν k A B C t ≠ 0 := ...
