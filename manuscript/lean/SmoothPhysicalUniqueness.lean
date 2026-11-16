/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetheredLyapunov.lean, line 1598

/-!
# manuscript.lean.SmoothPhysicalUniqueness

Machine-checked Lean 4 module.
-/

@[expose] public def SmoothPhysicalUniqueness (u₀ : VelocityField) (ν : ℝ) : Prop :=
  ∀ (T : ℝ) (u v : TimeDependentVelocity) (p q : TimeDependentPressure),
    IsLocalPhysicalSolution ν T u₀ u p → IsLocalPhysicalSolution ν T u₀ v q →
      ∀ t ∈ Set.Icc (0 : ℝ) T, u t = v t
