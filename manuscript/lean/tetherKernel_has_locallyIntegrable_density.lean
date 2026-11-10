-- FrohmanianTether/TetherWeight.lean, line 246
public theorem tetherKernel_has_locallyIntegrable_density :
    ∃ α, HasTetherKernelDensity TetherKernel α ∧
      ∀ ω, IsRegularVorticity ω → LocallyIntegrable (α ω) (MeasureTheory.volume : Measure T3) := ...
