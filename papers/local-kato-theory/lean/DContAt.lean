@[expose] public def R3BKMContinuationAt (ν : ℝ) (u₀ : VelocityField) : Prop :=
  (∃ Y : ℝ, ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsFeffermanSolutionOn ν T u₀ u p → ∀ t ∈ Set.Ico (0 : ℝ) T,
        BddAbove (Set.range fun x => ‖vorticity (u t) x‖) ∧ Mω u t ≤ Y) →
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure), FeffermanGlobalSolution ν u₀ u p
