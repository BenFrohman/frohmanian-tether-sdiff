-- FrohmanianTether/TetherImpliesBKM.lean, line 90
public theorem periodicBKMIntegrability_of_periodicTetherClosingBound {ν : ℝ}
    (h : PeriodicTetherClosingBound ν) (u₀ : VelocityField) (hdiv : ∀ x, div u₀ x = 0)
    (hsm : ContDiff ℝ (⊤ : ℕ∞) u₀) (hper : IsZ3Periodic u₀) :
    PeriodicBKMIntegrability ν u₀ := ...
