/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 49

/-!
# manuscript.lean.tp

Machine-checked Lean 4 module.
-/

@[expose] public def tp (k α β : ℝ) (j l : Fin 3) (y : T3) : ℝ :=
  α * Real.sin (k * y j) + β * Real.cos (k * y l)
