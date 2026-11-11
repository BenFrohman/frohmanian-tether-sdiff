-- FrohmanianTether/TetheredLyapunov.lean, line 1590
@[expose] public def BKMGlobalContinuation (u₀ : VelocityField) (ν : ℝ) : Prop :=
  Nonempty (KatoLocalWitness u₀ ν) → LocalFiniteTimeVorticityBound u₀ ν →
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      u 0 = u₀ ∧ NS_PDE u p ν ∧ (∀ t ≥ (0 : ℝ), ContDiff ℝ (⊤ : ℕ∞) (u t)) ∧
        IsPhysicalNSSolution u
