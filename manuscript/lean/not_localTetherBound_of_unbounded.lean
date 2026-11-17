/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherDefinitionAudit.lean, line 108

/-!
# manuscript.lean.not_localTetherBound_of_unbounded

Machine-checked Lean 4 module.
-/

public theorem not_localTetherBound_of_unbounded (ν : ℝ) {u₀ : VelocityField}
    (hsm : ContDiff ℝ (⊤ : ℕ∞) u₀) (hdiv : ∀ x, div u₀ x = 0)
    (hE : Integrable (fun x : T3 => ‖u₀ x‖ ^ 2))
    (hω : ¬ BddAbove (Set.range fun x => ‖vorticity u₀ x‖)) :
    ¬ TetheredLyapunov.LocalTetherBound u₀ ν := ...
