-- FrohmanianTether/StrainBoundRefutation.lean, line 78
public theorem not_forall_strain_le_sup_vorticity (C : ℝ) :
    ¬ ∀ (u : VelocityField) (x : T3),
      ‖fderiv ℝ u x‖ ≤ C * vorticity_sup_norm (curl u) := ...
