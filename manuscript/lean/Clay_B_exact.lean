/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
@[expose] public def Clay_B_exact : Prop :=
  ∀ (ν : ℝ) (u₀ : VelocityField),
    0 < ν →
    ContDiff ℝ (⊤ : ℕ∞) u₀ →
    (∀ x, div u₀ x = 0) →
    IsZ3Periodic u₀ →
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsPeriodicSmoothSolution ν u₀ (fun _ _ => 0) u p
