-- FrohmanianTether/TetherWeightProof.lean, line 436
public theorem tetherKernel_core_inputs :
    (∃ α, HasTetherKernelDensity TetherKernel α ∧
      ∀ ω, IsRegularVorticity ω → LocallyIntegrable (α ω) (MeasureTheory.volume : Measure T3)) ∧
    AEEnstrophyWeight TetherKernel ∧ SaturatesTetherQuadratic TetherKernel := ...
