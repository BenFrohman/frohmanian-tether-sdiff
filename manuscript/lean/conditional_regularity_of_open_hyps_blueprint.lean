-- FrohmanianTether/ClosureBlueprint.lean, line 201
public theorem conditional_regularity_of_open_hyps
    (u₀ : VelocityField) (ν : ℝ)
    (w : KatoLocalWitness u₀ ν)
    (hcont : TetheredLyapunov.BKMGlobalContinuation u₀ ν)
    (hRiccati : TetheredLyapunov.LocalTetherBound u₀ ν) :
    ∃ (u : ℝ → VelocityField) (p : ℝ → PressureField),
      NS_PDE u p ν ∧
      u 0 = u₀ ∧
      (∀ t ≥ (0 : ℝ), ContDiff ℝ (⊤ : ℕ∞) (u t)) ∧
      (∀ t ≥ (0 : ℝ), vorticity_sup_norm (vorticity (u t)) ≥ 0) ∧
      (∀ t ≥ (0 : ℝ), ∀ x, div (u t) x = 0) := ...
