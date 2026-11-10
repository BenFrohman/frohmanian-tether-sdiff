-- FrohmanianTether/Uniqueness.lean, line 633
public theorem uniqueness_of_minimal_tether_core
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (h_sym : ∀ ω F G, B ω F G = B ω G F)
    (h_proj : ∀ ω (F F' G : Functional),
      Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) =
        Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F' ω) → B ω F G = B ω F' G)
    (h_density : FactorsThroughProjection B → ∃ α, HasTetherKernelDensity B α ∧
      ∀ ω, IsRegularVorticity ω → LocallyIntegrable (α ω) (MeasureTheory.volume : Measure T3))
    (h_weight : AEEnstrophyWeight B)
    (h_sat : SaturatesTetherQuadratic B) :
    ∀ ω F G, B ω F G = TetherKernel ω F G := ...
