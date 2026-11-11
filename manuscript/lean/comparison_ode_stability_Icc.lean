-- FrohmanianTether/TetheredLyapunov.lean, line 1489
public theorem comparison_ode_stability_Icc
    (C κ'' : ℝ) (hC : 0 < C) (hκ : 0 < κ'') (y : ℝ → ℝ) (T : ℝ)
    (hdiff : ∀ s ∈ Set.Icc (0 : ℝ) T, DifferentiableAt ℝ y s)
    (hy_dot : ∀ s ∈ Set.Icc (0 : ℝ) T, deriv y s ≤ C * (y s) ^ 2 - κ'' * (y s) ^ 3)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    y t ≤ max (y 0) (C / κ'') := ...
