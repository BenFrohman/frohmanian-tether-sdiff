/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherWeight.lean, line 237

/-!
# manuscript.lean.not_aeEnstrophyWeightUnrestricted_of_eq_tether

Machine-checked Lean 4 module.
-/

public theorem not_aeEnstrophyWeightUnrestricted_of_eq_tether
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (hB : ∀ ω F G, B ω F G = TetherKernel ω F G) : ¬ AEEnstrophyWeightUnrestricted B := ...
