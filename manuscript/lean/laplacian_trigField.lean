/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 158

/-!
# manuscript.lean.laplacian_trigField

Machine-checked Lean 4 module.
-/

public theorem laplacian_trigField (k : ℝ) (α β : Fin 3 → ℝ) (j l : Fin 3 → Fin 3) (x : T3) :
    laplacian (trigField k α β j l) x = (-k ^ 2) • trigField k α β j l x := ...
