/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ClayStatements.lean, line 48

/-!
# manuscript.lean.FrohmanianTetherClosingBound

Machine-checked Lean 4 module.
-/

@[expose] public def FrohmanianTetherClosingBound (ν : ℝ) : Prop :=
  ∀ u₀ : VelocityField,
    (∀ x, div u₀ x = 0) → ContDiff ℝ (⊤ : ℕ∞) u₀ →
      Integrable (fun x : T3 => ‖u₀ x‖ ^ 2) →
        FrohmanianTetherBound u₀ ν
