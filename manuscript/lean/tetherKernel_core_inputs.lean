/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherWeightProof.lean, line 436

/-!
# manuscript.lean.tetherKernel_core_inputs

Machine-checked Lean 4 module.
-/

public theorem tetherKernel_core_inputs :
    (∃ α, HasTetherKernelDensity TetherKernel α ∧
      ∀ ω, IsRegularVorticity ω → LocallyIntegrable (α ω) (MeasureTheory.volume : Measure T3)) ∧
    AEEnstrophyWeight TetherKernel ∧ SaturatesTetherQuadratic TetherKernel := ...
