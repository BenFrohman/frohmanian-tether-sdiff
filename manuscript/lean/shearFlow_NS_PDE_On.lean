/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 363

/-!
# manuscript.lean.shearFlow_NS_PDE_On

Machine-checked Lean 4 module.
-/

public theorem shearFlow_NS_PDE_On (ν k a T : ℝ) :
    NS_PDE_On (shearFlow ν k a) shearPressure ν T := ...
