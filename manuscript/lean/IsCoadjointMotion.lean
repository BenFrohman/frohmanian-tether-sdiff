-- FrohmanianTether/PlanSteps.lean, line 61
def IsCoadjointMotion (SDiff : Type*) [Group SDiff] [MulAction SDiff CoadjointOrbit]
    (ω : ℝ → CoadjointOrbit) : Prop :=
  ∃ g : ℝ → SDiff, ∀ t, ω t = g t • ω 0
