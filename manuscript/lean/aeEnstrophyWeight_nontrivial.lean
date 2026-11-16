/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherWeightProof.lean, line 422

/-!
# manuscript.lean.aeEnstrophyWeight_nontrivial

Machine-checked Lean 4 module.
-/

public theorem aeEnstrophyWeight_nontrivial :
    HasTetherKernelDensity TetherKernel canonicalTetherDensity ∧
    (∀ ω, IsRegularVorticity ω →
      LocallyIntegrable (canonicalTetherDensity ω) (MeasureTheory.volume : Measure T3)) ∧
    IsRegularVorticity (rotOrbit 0) ∧ -kappa * Enstrophy (rotOrbit 0) ≠ 0 := ...
