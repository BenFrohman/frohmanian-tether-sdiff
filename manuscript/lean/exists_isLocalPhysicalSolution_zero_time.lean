/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherDefinitionAudit.lean, line 70

/-!
# manuscript.lean.exists_isLocalPhysicalSolution_zero_time

Machine-checked Lean 4 module.
-/

public theorem exists_isLocalPhysicalSolution_zero_time (ν : ℝ) {u₀ : VelocityField}
    (hsm : ContDiff ℝ (⊤ : ℕ∞) u₀) (hdiv : ∀ x, div u₀ x = 0)
    (hE : Integrable (fun x : T3 => ‖u₀ x‖ ^ 2)) :
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure), IsLocalPhysicalSolution ν 0 u₀ u p := ...
