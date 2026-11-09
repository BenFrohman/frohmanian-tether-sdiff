-- FrohmanianTether/SymplecticTether.lean, line 737
@[expose] public abbrev FrohmanianTetherRate (u₀ : VelocityField) (ν : ℝ) : Prop :=
  ∀ u : ℝ → VelocityField, ∀ p : ℝ → PressureField,
    0 < ν → NS_PDE u p ν → u 0 = u₀ → IsPhysicalNSSolution u →
      ∃ C κ'' : ℝ, 0 < C ∧ 0 < κ'' ∧
        (∀ s ≥ (0 : ℝ),
          DifferentiableAt ℝ (fun τ => vorticity_sup_norm (vorticity (u τ))) s) ∧
        (∀ s ≥ (0 : ℝ),
          deriv (fun τ => vorticity_sup_norm (vorticity (u τ))) s ≤
            C * vorticity_sup_norm (vorticity (u s)) ^ 2 -
              κ'' * vorticity_sup_norm (vorticity (u s)) ^ 3) ∧
        Continuous (fun τ : ℝ => vorticity_sup_norm (vorticity (u τ))) ∧
        (∀ τ ≥ (0 : ℝ), BddAbove (Set.range fun x => ‖vorticity (u τ) x‖))
