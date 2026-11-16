/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 233

/-!
# manuscript.lean.flow

Machine-checked Lean 4 module.
-/

@[expose] public def flow (ν k : ℝ) (α β : Fin 3 → ℝ) (j l : Fin 3 → Fin 3) :
    TimeDependentVelocity :=
  fun t y => decay (-(ν * k ^ 2)) t • trigField k α β j l y
