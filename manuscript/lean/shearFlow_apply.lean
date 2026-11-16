/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 328

/-!
# manuscript.lean.shearFlow_apply

Machine-checked Lean 4 module.
-/

public theorem shearFlow_apply (ν k a : ℝ) {t : ℝ} (ht : 0 ≤ t) (y : T3) :
    shearFlow ν k a t y =
      WithLp.toLp 2 ![Real.exp (-(ν * k ^ 2) * t) * a * Real.sin (k * y 2), 0, 0] := ...
