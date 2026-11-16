/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 208

/-!
# manuscript.lean.hasDerivAt_decay

Machine-checked Lean 4 module.
-/

public theorem hasDerivAt_decay (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (decay c) (c * decay c t) t := ...
