/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
@[expose] public def PeriodicBKMContinuation (ν : ℝ) : Prop :=
  ∀ u₀ : VelocityField,
    (∀ x, div u₀ x = 0) → ContDiff ℝ (⊤ : ℕ∞) u₀ → IsZ3Periodic u₀ →
      (∃ Y : ℝ, ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
        IsPeriodicSmoothSolutionOn ν T u₀ u p →
          ∀ t ∈ Set.Ico (0 : ℝ) T, vorticity_sup_norm (vorticity (u t)) ≤ Y) →
        ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
          IsPeriodicSmoothSolution ν u₀ (fun _ _ => 0) u p
