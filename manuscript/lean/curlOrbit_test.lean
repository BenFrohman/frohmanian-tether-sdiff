/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TestFieldFamily.lean, line 108

/-!
# manuscript.lean.curlOrbit_test

Machine-checked Lean 4 module.
-/

public theorem curlOrbit_test {H : T3 → ℝ} (hH : ContDiff ℝ ∞ H) (hc : HasCompactSupport H) :
    IsTestDirection (curlOrbit H hH) := ...
