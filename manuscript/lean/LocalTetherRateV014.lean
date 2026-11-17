/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherDefinitionAudit.lean, line 131

/-!
# manuscript.lean.LocalTetherRateV014

Machine-checked Lean 4 module.
-/

@[expose] public def LocalTetherRateV014 (u₀ : VelocityField) (ν : ℝ) : Prop :=
  ∃ C κ'' : ℝ, 0 < C ∧ 0 < κ'' ∧
    ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsLocalPhysicalSolution ν T u₀ u p →
        (∀ s ∈ Set.Icc (0 : ℝ) T,
          DifferentiableAt ℝ (fun τ => vorticity_sup_norm (vorticity (u τ))) s) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) T,
          deriv (fun τ => vorticity_sup_norm (vorticity (u τ))) s ≤
            C * vorticity_sup_norm (vorticity (u s)) ^ 2 -
              κ'' * vorticity_sup_norm (vorticity (u s)) ^ 3)
