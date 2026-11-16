/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherWeight.lean, line 246

/-!
# manuscript.lean.tetherKernel_has_locallyIntegrable_density

Machine-checked Lean 4 module.
-/

public theorem tetherKernel_has_locallyIntegrable_density :
    ∃ α, HasTetherKernelDensity TetherKernel α ∧
      ∀ ω, IsRegularVorticity ω → LocallyIntegrable (α ω) (MeasureTheory.volume : Measure T3) := ...
