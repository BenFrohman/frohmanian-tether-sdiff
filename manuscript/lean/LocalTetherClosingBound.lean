/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ClayStatements.lean, line 61

/-!
# manuscript.lean.LocalTetherClosingBound

Machine-checked Lean 4 module.
-/

@[expose] public def LocalTetherClosingBound (ν : ℝ) : Prop :=
  ∀ u₀ : VelocityField,
    (∀ x, div u₀ x = 0) → ContDiff ℝ (⊤ : ℕ∞) u₀ →
      Integrable (fun x : T3 => ‖u₀ x‖ ^ 2) →
        BddAbove (Set.range fun x => ‖vorticity u₀ x‖) →
          TetheredLyapunov.LocalTetherBound u₀ ν
