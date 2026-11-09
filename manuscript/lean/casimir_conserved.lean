-- FrohmanianTether/PlanSteps.lean, line 75
theorem casimir_conserved {SDiff : Type*} [Group SDiff] [MulAction SDiff CoadjointOrbit]
    (H : SDiffActionHyp SDiff) (ω : ℝ → CoadjointOrbit) (hω : IsCoadjointMotion SDiff ω)
    (f : ℝ → ℝ) (t : ℝ) : Casimir f (ω t) = Casimir f (ω 0) := ...
