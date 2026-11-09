/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
public theorem tethered_stretching_of_weight
    (ωField uField : VelocityField) (x : T3) (C M : ℝ)
    (hu : DifferentiableAt ℝ uField x)
    (hCZ : ‖fderiv ℝ uField x‖ ≤ C * vorticity_sup_norm ωField)
    (hmax : ‖ωField x‖ = M ∧ M = vorticity_sup_norm ωField)
    (orbit : CoadjointOrbit) (testF : Functional)
    (hweight : M ^ 4 ≤ Enstrophy orbit * ∫ y,
          ‖Pi_u (velocity_from_vorticity orbit)
              (FunctionalDerivative testF orbit) y‖ ^ 2 ∂volume) :
    inner ℝ (ωField x) (convective ωField uField x) +
        TetherKernel orbit testF testF ≤
      (C * M - kappa * M ^ 2) * M ^ 2 := ...
