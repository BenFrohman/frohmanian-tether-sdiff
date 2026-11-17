/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherImpliesBKM.lean, line 69

/-!
# manuscript.lean.periodicBKMIntegrability_of_periodicTetherBound

Machine-checked Lean 4 module.
-/

public theorem periodicBKMIntegrability_of_periodicTetherBound {ν : ℝ} {u₀ : VelocityField}
    (h : PeriodicTetherBound ν u₀) : PeriodicBKMIntegrability ν u₀ := ...
