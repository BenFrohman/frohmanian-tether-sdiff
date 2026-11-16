/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/NS_Equations.lean, line 2270

/-!
# manuscript.lean.IsPhysicalNSSolution

Machine-checked Lean 4 module.
-/

@[expose] public def IsPhysicalNSSolution (u : TimeDependentVelocity) : Prop :=
  (∀ t ≥ (0 : ℝ), ∀ x : T3, DifferentiableAt ℝ (fun s => u s x) t) ∧
  (∀ t ≥ (0 : ℝ), Continuous (u t)) ∧
  (∀ t ≥ (0 : ℝ), Integrable (fun x : T3 => ‖u t x‖ ^ 2)) ∧
  (∀ t ≥ (0 : ℝ), (∫ x, ‖u t x‖ ^ 2 ∂volume) ≤ ∫ x, ‖u 0 x‖ ^ 2 ∂volume) ∧
  (∃ v₀ : VelocityField, ∀ t ≤ (0 : ℝ), u t = u 0 + t • v₀)
