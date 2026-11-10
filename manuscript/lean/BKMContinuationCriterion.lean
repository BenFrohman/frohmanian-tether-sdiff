-- FrohmanianTether/NS_Equations.lean, line 3134
@[expose] public def BKMContinuationCriterion (u : TimeDependentVelocity) (ν : ℝ) : Prop :=
  ∀ T : ℝ, Tstar (u 0) ν = (T : EReal) →
    ¬ IntegrableOn (fun t => vorticity_sup_norm (vorticity (u t))) (Set.Icc 0 T)
