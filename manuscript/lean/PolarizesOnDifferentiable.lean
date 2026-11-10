-- FrohmanianTether/Uniqueness.lean, line 292
@[expose] public def PolarizesOnDifferentiable
    (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  ∀ (ω : CoadjointOrbit) (F G : Functional),
    (∃ g, IsFunctionalGradient F ω g) → (∃ g, IsFunctionalGradient G ω g) →
    2 * B ω F G =
      B ω (fun ω' => F ω' + G ω') (fun ω' => F ω' + G ω') - B ω F F - B ω G G
