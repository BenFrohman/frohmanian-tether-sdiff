/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherNondegeneracy.lean, line 390

/-!
# manuscript.lean.not_tetherKernel_polarizes

Machine-checked Lean 4 module.
-/

public theorem not_tetherKernel_polarizes :
    ¬ ∀ ω F G, 2 * TetherKernel ω F G = TetherKernel ω (fun η => F η + G η) (fun η => F η + G η) - TetherKernel ω F F - TetherKernel ω G G := ...
