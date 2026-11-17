/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetheredLyapunov.lean, line 1412

/-!
# manuscript.lean.PhysicalBKMContinuationCriterionFor

Machine-checked Lean 4 module.
-/

@[expose] public def PhysicalBKMContinuationCriterionFor (u₀ : VelocityField) (ν : ℝ) : Prop :=
  ∀ u : ℝ → VelocityField, ∀ p : ℝ → PressureField,
    NS_PDE u p ν → u 0 = u₀ → IsPhysicalNSSolution u → BKMContinuationCriterion u ν
