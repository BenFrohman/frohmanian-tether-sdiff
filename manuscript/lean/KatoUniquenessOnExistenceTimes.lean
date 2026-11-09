-- FrohmanianTether/TetheredLyapunov.lean, line 1930
@[expose] public def KatoUniquenessOnExistenceTimes (u₀ : VelocityField) (ν : ℝ)
    (w : KatoLocalWitness u₀ ν) : Prop :=
  ∀ (T' : ℝ) (v : TimeDependentVelocity) (q : TimeDependentPressure),
    T' ∈ existenceTimes u₀ ν → v 0 = u₀ → NS_PDE v q ν →
    (∀ t ∈ Set.Icc (0 : ℝ) T', ContDiff ℝ (⊤ : ℕ∞) (v t)) →
    IsPhysicalNSSolution v →
    ∀ t ∈ Set.Icc (0 : ℝ) T', w.u t = v t
