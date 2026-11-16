/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ClayStatements.lean, line 575

/-!
# manuscript.lean.PeriodicTetherClosingBound

Machine-checked Lean 4 module.
-/

@[expose] public def PeriodicTetherClosingBound (ν : ℝ) : Prop :=
  ∀ u₀ : VelocityField,
    (∀ x, div u₀ x = 0) → ContDiff ℝ (⊤ : ℕ∞) u₀ → IsZ3Periodic u₀ →
      ∃ Y : ℝ, ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
        IsPeriodicSmoothSolutionOn ν T u₀ u p →
          ∀ t ∈ Set.Ico (0 : ℝ) T, vorticity_sup_norm (vorticity (u t)) ≤ Y
