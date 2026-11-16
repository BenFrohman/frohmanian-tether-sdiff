/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 594

/-!
# manuscript.lean.shearFlow_ne_zero

Machine-checked Lean 4 module.
-/

public theorem shearFlow_ne_zero (ν : ℝ) {k a : ℝ} (hk : k ≠ 0) (ha : a ≠ 0) {t : ℝ}
    (ht : 0 ≤ t) : shearFlow ν k a t ≠ 0 := ...
