/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ArnoldGeometric.lean, line 328

/-!
# manuscript.lean.DivFreeL2

Machine-checked Lean 4 module.
-/

@[expose] public noncomputable def DivFreeL2 : Submodule ℝ L2Field := (Submodule.span ℝ testFields).topologicalClosure
