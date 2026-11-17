@[expose] public def FrohmanianTetherRateSmooth (u₀ : VelocityField) (ν : ℝ) : Prop :=
  ∃ C kap : ℝ, 0 < C ∧ 0 < kap ∧
    ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsFeffermanSolutionOn ν T u₀ u p →
        ContinuousOn (Mω u) (Set.Ico (0 : ℝ) T) ∧
        (∀ s ∈ Set.Ico (0 : ℝ) T, ∃ d : ℝ,
          HasDerivWithinAt (Mω u) d (Set.Ici s) s ∧ d ≤ C * Mω u s ^ 2 - kap * Mω u s ^ 3) ∧
        (∀ t ∈ Set.Ico (0 : ℝ) T, BddAbove (Set.range fun x => ‖vorticity (u t) x‖))
