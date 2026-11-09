/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
public theorem comparison_ode_stability
    (C κ'' : ℝ) (hC : 0 < C) (hκ : 0 < κ'')
    (y : ℝ → ℝ)
    (hdiff : ∀ s ≥ (0 : ℝ), DifferentiableAt ℝ y s)
    (hy_dot : ∀ s ≥ (0 : ℝ), deriv y s ≤ C * (y s) ^ 2 - κ'' * (y s) ^ 3)
    (t : ℝ) (ht : 0 ≤ t) :
    y t ≤ max (y 0) (C / κ'') := ...
