/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 130

/-!
# manuscript.lean.trigField

Machine-checked Lean 4 module.
-/

@[expose] public def trigField (k : ℝ) (α β : Fin 3 → ℝ) (j l : Fin 3 → Fin 3) : VelocityField :=
  fun y => WithLp.toLp 2 (fun i => tp k (α i) (β i) (j i) (l i) y)
