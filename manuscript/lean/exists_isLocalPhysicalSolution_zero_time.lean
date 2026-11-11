-- FrohmanianTether/TetherDefinitionAudit.lean, line 70
public theorem exists_isLocalPhysicalSolution_zero_time (ν : ℝ) {u₀ : VelocityField}
    (hsm : ContDiff ℝ (⊤ : ℕ∞) u₀) (hdiv : ∀ x, div u₀ x = 0)
    (hE : Integrable (fun x : T3 => ‖u₀ x‖ ^ 2)) :
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure), IsLocalPhysicalSolution ν 0 u₀ u p := ...
