/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- Scratch/R3BKMContinuation.lean, lines 49-49

/-!
# papers.local-kato-theory.lean.DhsSq

Verbatim excerpt (statement only) of the kernel-checked source file named above.
-/

def hsSq (m : ℕ) (f : VelocityField) : ℝ := (sobolevEnergy m f).toReal
