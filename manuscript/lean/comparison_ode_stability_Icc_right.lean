/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetheredLyapunov.lean, line 1520

/-!
# manuscript.lean.comparison_ode_stability_Icc_right

Machine-checked Lean 4 module.
-/

public theorem comparison_ode_stability_Icc_right
    (C κ'' : ℝ) (hC : 0 < C) (hκ : 0 < κ'') (y : ℝ → ℝ) (T : ℝ)
    (hcont : ContinuousOn y (Set.Icc (0 : ℝ) T))
    (hright : ∀ s ∈ Set.Ico (0 : ℝ) T, ∃ d : ℝ,
      HasDerivWithinAt y d (Set.Ici s) s ∧ d ≤ C * (y s) ^ 2 - κ'' * (y s) ^ 3)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    y t ≤ max (y 0) (C / κ'') := ...
