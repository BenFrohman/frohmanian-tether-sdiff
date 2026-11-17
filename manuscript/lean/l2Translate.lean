/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherEquivariantC1.lean, line 118

/-!
# manuscript.lean.l2Translate

Machine-checked Lean 4 module.
-/

@[expose] public def l2Translate (h : T3) : L2Field →ₗᵢ[ℝ] L2Field :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x : T3 => x - h) (mp_sub h)
