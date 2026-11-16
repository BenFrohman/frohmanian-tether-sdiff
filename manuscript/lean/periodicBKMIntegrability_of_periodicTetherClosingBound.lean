/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherImpliesBKM.lean, line 90

/-!
# manuscript.lean.periodicBKMIntegrability_of_periodicTetherClosingBound

Machine-checked Lean 4 module.
-/

public theorem periodicBKMIntegrability_of_periodicTetherClosingBound {ν : ℝ}
    (h : PeriodicTetherClosingBound ν) (u₀ : VelocityField) (hdiv : ∀ x, div u₀ x = 0)
    (hsm : ContDiff ℝ (⊤ : ℕ∞) u₀) (hper : IsZ3Periodic u₀) :
    PeriodicBKMIntegrability ν u₀ := ...
