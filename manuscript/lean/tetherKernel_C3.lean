-- FrohmanianTether/SymplecticTether.lean, line 433
public theorem tetherKernel_C3 (F : Functional) (ω : CoadjointOrbit) :
    TetherKernel ω F F ≤
      -kappa * Enstrophy ω * ∫ x,
          ‖Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x‖ ^ 2
        ∂volume := ...
