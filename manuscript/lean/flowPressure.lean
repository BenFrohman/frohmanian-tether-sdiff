/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 248

/-!
# manuscript.lean.flowPressure

Machine-checked Lean 4 module.
-/

@[expose] public def flowPressure (ν k : ℝ) (p₀ : PressureField) : TimeDependentPressure :=
  fun t y => decay (-(ν * k ^ 2)) t ^ 2 * p₀ y
