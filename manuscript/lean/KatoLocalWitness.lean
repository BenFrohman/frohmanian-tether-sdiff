/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/NS_Equations.lean, line 2486

/-!
# manuscript.lean.KatoLocalWitness

Machine-checked Lean 4 module.
-/

public structure KatoLocalWitness (u₀ : VelocityField) (ν : ℝ) where
  T : ℝ
  Tpos : 0 < T
  u : TimeDependentVelocity
  p : TimeDependentPressure
  smooth : ∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (⊤ : ℕ∞) (u t)
  init : u 0 = u₀
  pde : NS_PDE_On u p ν T
  phys : IsPhysicalNSSolutionOn u T
