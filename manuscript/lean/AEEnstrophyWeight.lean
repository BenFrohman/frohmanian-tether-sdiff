-- FrohmanianTether/Uniqueness.lean, line 527
@[expose] public def AEEnstrophyWeight
    (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  ∀ α, HasTetherKernelDensity B α →
    (∀ ω, IsRegularVorticity ω → LocallyIntegrable (α ω) (MeasureTheory.volume : Measure T3)) →
    ∃ c : ℝ, ∀ ω, IsRegularVorticity ω →
      ∀ᵐ x ∂(MeasureTheory.volume : Measure T3), α ω x = -c * Enstrophy ω
