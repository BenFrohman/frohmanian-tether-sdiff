-- FrohmanianTether/TetherWeightProof.lean, line 422
public theorem aeEnstrophyWeight_nontrivial :
    HasTetherKernelDensity TetherKernel canonicalTetherDensity ∧
    (∀ ω, IsRegularVorticity ω →
      LocallyIntegrable (canonicalTetherDensity ω) (MeasureTheory.volume : Measure T3)) ∧
    IsRegularVorticity (rotOrbit 0) ∧ -kappa * Enstrophy (rotOrbit 0) ≠ 0 := ...
