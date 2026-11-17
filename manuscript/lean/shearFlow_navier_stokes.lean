/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 347

/-!
# manuscript.lean.shearFlow_navier_stokes

Machine-checked Lean 4 module.
-/

public theorem shearFlow_navier_stokes (ν k a : ℝ) :
    navier_stokes_eq (shearFlow ν k a) shearPressure ν := ...
