-- FrohmanianTether/TetherImpliesBKM.lean, line 53
@[expose] public def PeriodicBKMIntegrability (ν : ℝ) (u₀ : VelocityField) : Prop :=
  ∀ T₀ : ℝ, ∃ C : ℝ≥0∞, C < ⊤ ∧
    ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
      T ≤ T₀ → IsPeriodicSmoothSolutionOn ν T u₀ u p →
        ∫⁻ t in Set.Ico (0 : ℝ) T, ENNReal.ofReal (vorticity_sup_norm (vorticity (u t))) ≤ C
