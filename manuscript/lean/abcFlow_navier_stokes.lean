/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 450

/-!
# manuscript.lean.abcFlow_navier_stokes

Machine-checked Lean 4 module.
-/

public theorem abcFlow_navier_stokes (ν k A B C : ℝ) :
    navier_stokes_eq (abcFlow ν k A B C) (abcPressure ν k A B C) ν := ...
