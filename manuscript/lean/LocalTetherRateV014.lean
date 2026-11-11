-- FrohmanianTether/TetherDefinitionAudit.lean, line 131
@[expose] public def LocalTetherRateV014 (u₀ : VelocityField) (ν : ℝ) : Prop :=
  ∃ C κ'' : ℝ, 0 < C ∧ 0 < κ'' ∧
    ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsLocalPhysicalSolution ν T u₀ u p →
        (∀ s ∈ Set.Icc (0 : ℝ) T,
          DifferentiableAt ℝ (fun τ => vorticity_sup_norm (vorticity (u τ))) s) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) T,
          deriv (fun τ => vorticity_sup_norm (vorticity (u τ))) s ≤
            C * vorticity_sup_norm (vorticity (u s)) ^ 2 -
              κ'' * vorticity_sup_norm (vorticity (u s)) ^ 3)
