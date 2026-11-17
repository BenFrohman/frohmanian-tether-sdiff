/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/PlanSteps.lean, line 76

/-!
# manuscript.lean.tether_bound_not_scale_invariant

Machine-checked Lean 4 module.
-/

theorem tether_bound_not_scale_invariant (S C κ M : ℝ) (hκ : 0 < κ) (hM : M ≠ 0) :
    ¬ ∀ l : ℝ, 0 < l → l ^ 6 * S ≤ C * (l ^ 2 * M) ^ 3 - κ * (l ^ 2 * M) ^ 4 := ...
