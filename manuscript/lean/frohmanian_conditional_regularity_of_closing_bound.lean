-- FrohmanianTether/ClayStatements.lean, line 159
public theorem frohmanian_conditional_regularity_of_closing_bound
    (ν : ℝ) (hν : 0 < ν)
    (hclose : LocalTetherClosingBound ν)
    (hKato : ∀ u₀ : VelocityField, ContDiff ℝ (⊤ : ℕ∞) u₀ → (∀ x, div u₀ x = 0) →
      Integrable (fun x : T3 => ‖u₀ x‖ ^ 2) → KatoLocalWitness u₀ ν)
    (hcont : ∀ u₀ : VelocityField, TetheredLyapunov.BKMGlobalContinuation u₀ ν)
    (huniq : ∀ u₀ : VelocityField, TetheredLyapunov.SmoothPhysicalUniqueness u₀ ν)
    (u₀ : VelocityField) (hdiv : ∀ x, div u₀ x = 0) (hsm : ContDiff ℝ (⊤ : ℕ∞) u₀)
    (hE : Integrable (fun x : T3 => ‖u₀ x‖ ^ 2))
    (hω₀ : BddAbove (Set.range fun x => ‖vorticity u₀ x‖)) :
    ∃ (u : TimeDependentVelocity),
      (∀ t ≥ (0 : ℝ), ConditionalRegularity.IsSmooth (u t)) ∧
      (u 0 = u₀) ∧
      (∀ t ≥ (0 : ℝ), ConditionalRegularity.satisfies_NavierStokes u ν) ∧
      (∀ t ≥ (0 : ℝ), ConditionalRegularity.vorticity_sup_norm (vorticity (u t)) ≥ 0) ∧
      (∀ v : TimeDependentVelocity,
        (∀ t ≥ (0 : ℝ), ConditionalRegularity.IsSmooth (v t)) →
        v 0 = u₀ →
        (∀ t ≥ (0 : ℝ), ConditionalRegularity.satisfies_NavierStokes v ν) →
        ∀ t ≥ (0 : ℝ), v t = u t) := ...
