-- FrohmanianTether/TetherWeightProof.lean, line 89
public theorem integral_beta_eq_zero {α : CoadjointOrbit → T3 → ℝ}
    (hα : HasTetherKernelDensity TetherKernel α) {ω : CoadjointOrbit} (hω : IsRegularVorticity ω)
    (hloc : LocallyIntegrable (α ω) (MeasureTheory.volume : Measure T3))
    {a b : CoadjointOrbit} (ha : IsTestDirection a) (hb : IsTestDirection b)
    (ha0 : projCoef ω a.val = 0) (hb0 : projCoef ω b.val = 0) :
    ∫ x, (α ω x + kappa * Enstrophy ω) * inner ℝ (a.val x) (b.val x) ∂MeasureTheory.volume = 0 := ...
