-- FrohmanianTether/Uniqueness.lean, line 566
@[expose] public def AEEnstrophyWeight
    (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  ∀ α, HasTetherKernelDensity B α → ∃ c : ℝ, ∀ ω, IsRegularVorticity ω →
    ∀ᵐ x ∂(MeasureTheory.volume : Measure T3), α ω x = -c * Enstrophy ω
