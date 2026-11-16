/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TestFieldFamily.lean, line 76

/-!
# manuscript.lean.div_curlVal

Machine-checked Lean 4 module.
-/

public theorem div_curlVal {H : T3 → ℝ} (hH : ContDiff ℝ ∞ H) (x : T3) :
    NavierStokes3D.div (curlVal H) x = 0 := ...
