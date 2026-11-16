/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 184

/-!
# manuscript.lean.decay

Machine-checked Lean 4 module.
-/

@[expose] public def decay (c t : ℝ) : ℝ := if 0 ≤ t then Real.exp (c * t) else 1 + c * t
