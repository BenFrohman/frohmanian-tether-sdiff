/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 459

/-!
# manuscript.lean.abcFlow_NS_PDE_On

Machine-checked Lean 4 module.
-/

public theorem abcFlow_NS_PDE_On (ν k A B C T : ℝ) :
    NS_PDE_On (abcFlow ν k A B C) (abcPressure ν k A B C) ν T := ...
