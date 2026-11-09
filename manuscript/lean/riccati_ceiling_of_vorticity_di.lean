/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
public theorem riccati_ceiling_of_vorticity_di
    (u : TimeDependentVelocity) (C κ'' : ℝ)
    (hC : 0 < C) (hκ : 0 < κ'')
    (hdiff : ∀ s ≥ (0 : ℝ),
      DifferentiableAt ℝ (fun τ => vorticity_sup_norm (vorticity (u τ))) s)
    (hDI : ∀ s ≥ (0 : ℝ),
      deriv (fun τ => vorticity_sup_norm (vorticity (u τ))) s ≤
        C * vorticity_sup_norm (vorticity (u s)) ^ 2 -
          κ'' * vorticity_sup_norm (vorticity (u s)) ^ 3)
    (hcont : Continuous fun τ : ℝ => vorticity_sup_norm (vorticity (u τ))) :
    ∃ Y : ℝ,
      (∀ τ ≥ (0 : ℝ), vorticity_sup_norm (vorticity (u τ)) ≤ Y) ∧
      Continuous (fun τ : ℝ => vorticity_sup_norm (vorticity (u τ))) := ...
