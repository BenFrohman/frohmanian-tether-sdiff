/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherImpliesBKM.lean, line 53

/-!
# manuscript.lean.PeriodicBKMIntegrability

Machine-checked Lean 4 module.
-/

@[expose] public def PeriodicBKMIntegrability (ν : ℝ) (u₀ : VelocityField) : Prop :=
  ∀ T₀ : ℝ, ∃ C : ℝ≥0∞, C < ⊤ ∧
    ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
      T ≤ T₀ → IsPeriodicSmoothSolutionOn ν T u₀ u p →
        ∫⁻ t in Set.Ico (0 : ℝ) T, ENNReal.ofReal (vorticity_sup_norm (vorticity (u t))) ≤ C
