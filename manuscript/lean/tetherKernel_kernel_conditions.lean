/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/Uniqueness.lean, line 605

/-!
# manuscript.lean.tetherKernel_kernel_conditions

Machine-checked Lean 4 module.
-/

public theorem tetherKernel_kernel_conditions :
    SaturatesTetherQuadratic TetherKernel ∧
    (∀ ω (F F' G : Functional),
      Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) =
        Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F' ω) →
        TetherKernel ω F G = TetherKernel ω F' G) ∧
    HasTetherKernelDensity TetherKernel canonicalTetherDensity ∧
    PolarizesOnDifferentiable TetherKernel ∧
    (∃ ω F, TetherKernel ω F F ≠ 0) := ...
