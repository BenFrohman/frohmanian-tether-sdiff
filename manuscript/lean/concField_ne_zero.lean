/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TestFieldFamily.lean, line 130

/-!
# manuscript.lean.concField_ne_zero

Machine-checked Lean 4 module.
-/

public theorem concField_ne_zero (x : T3) {r : ℝ} (hr : 0 < r) :
    ∃ y, (concField x hr).val y ≠ 0 := ...
