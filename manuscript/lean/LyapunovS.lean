/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
public noncomputable def LyapunovS (ωε : VorticityField) (phi : T3 → ℝ) : ℝ :=
  ∫ x, (1 / 2) * ‖ωε x‖ ^ 2 + (kappa / 4) * ‖ωε x‖ ^ 4 * phi x ∂volume
