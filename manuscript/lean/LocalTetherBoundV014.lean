/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherDefinitionAudit.lean, line 54

/-!
# manuscript.lean.LocalTetherBoundV014

Machine-checked Lean 4 module.
-/

@[expose] public def LocalTetherBoundV014 (u₀ : VelocityField) (ν : ℝ) : Prop :=
  ∃ Y : ℝ, ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
    IsLocalPhysicalSolution ν T u₀ u p →
      ∀ t ∈ Set.Icc (0 : ℝ) T, vorticity_sup_norm (vorticity (u t)) ≤ Y
