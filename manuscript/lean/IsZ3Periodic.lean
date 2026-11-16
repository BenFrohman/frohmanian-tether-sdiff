/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ClayStatements.lean, line 214

/-!
# manuscript.lean.IsZ3Periodic

Machine-checked Lean 4 module.
-/

@[expose] public def IsZ3Periodic {α : Type*} (f : T3 → α) : Prop :=
  ∀ (k : Fin 3 → ℤ) (x : T3), f (x + latticeVec k) = f x
