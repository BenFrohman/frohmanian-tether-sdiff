/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetheredLyapunov.lean, line 1463

/-!
# manuscript.lean.LocalTetherBound

Machine-checked Lean 4 module.
-/

@[expose] public def LocalTetherBound (u₀ : VelocityField) (ν : ℝ) : Prop :=
  ∃ Y : ℝ, ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
    IsLocalPhysicalSolution ν T u₀ u p →
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        BddAbove (Set.range fun x => ‖vorticity (u t) x‖) ∧
          vorticity_sup_norm (vorticity (u t)) ≤ Y
