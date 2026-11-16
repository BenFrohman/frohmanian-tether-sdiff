/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherImpliesBKM.lean, line 61

/-!
# manuscript.lean.periodicTetherClosingBound_iff

Machine-checked Lean 4 module.
-/

public theorem periodicTetherClosingBound_iff (ν : ℝ) :
    PeriodicTetherClosingBound ν ↔
      ∀ u₀ : VelocityField, (∀ x, div u₀ x = 0) → ContDiff ℝ (⊤ : ℕ∞) u₀ → IsZ3Periodic u₀ →
        PeriodicTetherBound ν u₀ := ...
