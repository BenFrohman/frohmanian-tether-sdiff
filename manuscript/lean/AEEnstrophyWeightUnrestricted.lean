-- FrohmanianTether/Uniqueness.lean, line 517
@[expose] public def AEEnstrophyWeightUnrestricted
    (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  ∀ α, HasTetherKernelDensity B α → ∃ c : ℝ, ∀ ω, IsRegularVorticity ω →
    ∀ᵐ x ∂(MeasureTheory.volume : Measure T3), α ω x = -c * Enstrophy ω
