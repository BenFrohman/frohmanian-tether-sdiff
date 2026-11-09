-- FrohmanianTether/Uniqueness.lean, line 583
public theorem uniqueness_of_minimal_tether_core
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (h_sym : ∀ ω F G, B ω F G = B ω G F)
    (h_proj : ∀ ω (F F' G : Functional),
      Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) =
        Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F' ω) → B ω F G = B ω F' G)
    (h_density : FactorsThroughProjection B → ∃ α, HasTetherKernelDensity B α)
    (h_weight : ∀ α, HasTetherKernelDensity B α → ∃ c : ℝ, ∀ ω x, α ω x = -c * Enstrophy ω)
    (h_sat : SaturatesTetherQuadratic B)
    (h_nondeg : ∃ (ω : CoadjointOrbit) (F : Functional), Enstrophy ω * (∫ x,
        inner ℝ (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x)
          (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x) ∂NavierStokes3D.volume) ≠ 0) :
    ∀ ω F G, B ω F G = TetherKernel ω F G := ...
