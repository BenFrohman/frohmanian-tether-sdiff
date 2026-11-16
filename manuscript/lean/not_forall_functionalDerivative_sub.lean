/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherNondegeneracy.lean, line 419

/-!
# manuscript.lean.not_forall_functionalDerivative_sub

Machine-checked Lean 4 module.
-/

public theorem not_forall_functionalDerivative_sub :
    ¬ ∀ ω (F F' : CoadjointOrbit → ℝ), FunctionalDerivative (fun η => F η - F' η) ω =
      FunctionalDerivative F ω - FunctionalDerivative F' ω := ...
