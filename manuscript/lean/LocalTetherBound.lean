-- FrohmanianTether/TetheredLyapunov.lean, line 1463
@[expose] public def LocalTetherBound (u₀ : VelocityField) (ν : ℝ) : Prop :=
  ∃ Y : ℝ, ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
    IsLocalPhysicalSolution ν T u₀ u p →
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        BddAbove (Set.range fun x => ‖vorticity (u t) x‖) ∧
          vorticity_sup_norm (vorticity (u t)) ≤ Y
