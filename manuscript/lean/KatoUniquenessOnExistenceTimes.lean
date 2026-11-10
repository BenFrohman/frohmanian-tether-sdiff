-- FrohmanianTether/TetheredLyapunov.lean, line 1427
@[expose] public def KatoUniquenessOnExistenceTimes (u₀ : VelocityField) (ν : ℝ)
    (w : KatoLocalWitness u₀ ν) : Prop :=
  ∀ (T' : ℝ) (v : TimeDependentVelocity) (q : TimeDependentPressure),
    T' ∈ existenceTimes u₀ ν → v 0 = u₀ → NS_PDE_On v q ν T' →
    (∀ t ∈ Set.Icc (0 : ℝ) T', ContDiff ℝ (⊤ : ℕ∞) (v t)) →
    IsPhysicalNSSolutionOn v T' →
    ∀ t ∈ Set.Icc (0 : ℝ) T', w.u t = v t
