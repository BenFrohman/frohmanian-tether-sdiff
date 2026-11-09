/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
public theorem stretching_inner_le_at_max
    (ω u : VelocityField) (x : T3) (C_CZ : ℝ)
    (hu : DifferentiableAt ℝ u x)
    (hCZ : PointwiseStrainSupBound u ω C_CZ x)
    (hmax : ‖ω x‖ = vorticity_sup_norm ω) :
    inner ℝ (ω x) (convective ω u x) ≤
      C_CZ * vorticity_sup_norm ω ^ 3 := ...
