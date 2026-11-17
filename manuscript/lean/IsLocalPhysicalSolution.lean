/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/NS_Equations.lean, line 2329

/-!
# manuscript.lean.IsLocalPhysicalSolution

Machine-checked Lean 4 module.
-/

@[expose] public def IsLocalPhysicalSolution (ν T : ℝ) (u₀ : VelocityField)
    (u : TimeDependentVelocity) (p : TimeDependentPressure) : Prop :=
  u 0 = u₀ ∧ NS_PDE_On u p ν T ∧ (∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (⊤ : ℕ∞) (u t)) ∧
    IsPhysicalNSSolutionOn u T
