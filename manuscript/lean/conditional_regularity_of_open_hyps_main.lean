-- FrohmanianTether/ConditionalRegularity.lean, line 136
public theorem conditional_regularity_of_open_hyps
    (u0 : TimeDependentVelocity)
    (_h_div_free : ∀ t x, div (u0 t) x = 0)
    (_h_smooth : IsSmooth (u0 0))
    (_h_finite_energy : Integrable (fun x : T3 => ‖u0 0 x‖ ^ 2))
    (ν : ℝ) (_h_ν_pos : ν > 0)
    (w : KatoLocalWitness (u0 0) ν)
    (hcont : TetheredLyapunov.BKMGlobalContinuation (u0 0) ν)
    (hRiccati : TetheredLyapunov.LocalTetherBound (u0 0) ν)
    (huniq : TetheredLyapunov.SmoothPhysicalUniqueness (u0 0) ν) :
  ∃ (u : TimeDependentVelocity),
    (∀ t ≥ (0 : ℝ), IsSmooth (u t)) ∧
    (u 0 = u0 0) ∧
    (∀ t ≥ (0 : ℝ), satisfies_NavierStokes u ν) ∧
    (∀ t ≥ (0 : ℝ), vorticity_sup_norm (vorticity (u t)) ≥ 0) ∧
    (∀ v : TimeDependentVelocity,
      (∀ t ≥ (0 : ℝ), IsSmooth (v t)) →
      v 0 = u0 0 →
      (∀ t ≥ (0 : ℝ), satisfies_NavierStokes v ν) →
      ∀ t ≥ (0 : ℝ), v t = u t) := ...
