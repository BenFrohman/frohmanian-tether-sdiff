/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherImpliesBKM.lean, line 45

/-!
# manuscript.lean.PeriodicTetherBound

Machine-checked Lean 4 module.
-/

@[expose] public def PeriodicTetherBound (ν : ℝ) (u₀ : VelocityField) : Prop :=
  ∃ Y : ℝ, ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
    IsPeriodicSmoothSolutionOn ν T u₀ u p →
      ∀ t ∈ Set.Ico (0 : ℝ) T, vorticity_sup_norm (vorticity (u t)) ≤ Y
