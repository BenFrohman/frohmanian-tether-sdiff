-- FrohmanianTether/Uniqueness.lean, line 604
public theorem tetherKernel_kernel_conditions :
    SaturatesTetherQuadratic TetherKernel ∧
    (∀ ω (F F' G : Functional),
      Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) =
        Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F' ω) →
        TetherKernel ω F G = TetherKernel ω F' G) ∧
    HasTetherKernelDensity TetherKernel canonicalTetherDensity ∧
    PolarizesOnDifferentiable TetherKernel ∧
    (∃ ω F, TetherKernel ω F F ≠ 0) := ...
