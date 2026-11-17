/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- Scratch/RepairedTetherRate.lean, lines 78-79

/-!
# papers.local-kato-theory.lean.DMw

Verbatim excerpt (statement only) of the kernel-checked source file named above.
-/

@[expose] public def Mω (u : TimeDependentVelocity) (t : ℝ) : ℝ :=
  vorticity_sup_norm (vorticity (u t))
