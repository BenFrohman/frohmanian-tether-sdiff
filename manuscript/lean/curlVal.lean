/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TestFieldFamily.lean, line 38

/-!
# manuscript.lean.curlVal

Machine-checked Lean 4 module.
-/

@[expose] public def curlVal (H : T3 → ℝ) (y : T3) : EuclideanSpace ℝ (Fin 3) :=
  pd H 1 y • eb 0 - pd H 0 y • eb 1
