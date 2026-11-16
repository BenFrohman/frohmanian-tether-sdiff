/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/Uniqueness.lean, line 481

/-!
# manuscript.lean.not_pointwiseEnstrophyWeight_of_density

Machine-checked Lean 4 module.
-/

public theorem not_pointwiseEnstrophyWeight_of_density
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (hex : ∃ α, HasTetherKernelDensity B α) : ¬ PointwiseEnstrophyWeight B := ...
