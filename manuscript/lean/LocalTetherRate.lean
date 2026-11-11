-- FrohmanianTether/TetheredLyapunov.lean, line 1559
@[expose] public def LocalTetherRate (u₀ : VelocityField) (ν : ℝ) : Prop :=
  ∃ C κ'' : ℝ, 0 < C ∧ 0 < κ'' ∧
    ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsLocalPhysicalSolution ν T u₀ u p →
        ContinuousOn (fun τ => vorticity_sup_norm (vorticity (u τ))) (Set.Icc (0 : ℝ) T) ∧
        (∀ s ∈ Set.Ico (0 : ℝ) T, ∃ d : ℝ,
          HasDerivWithinAt (fun τ => vorticity_sup_norm (vorticity (u τ))) d (Set.Ici s) s ∧
            d ≤ C * vorticity_sup_norm (vorticity (u s)) ^ 2 -
              κ'' * vorticity_sup_norm (vorticity (u s)) ^ 3) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) T, BddAbove (Set.range fun x => ‖vorticity (u t) x‖))
