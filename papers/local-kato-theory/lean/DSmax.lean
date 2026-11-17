/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- Scratch/KatoMaximal.lean, lines 565-565

/-!
# papers.local-kato-theory.lean.DSmax

Verbatim excerpt (statement only) of the kernel-checked source file named above.
-/

def Smax {k : ℕ} (hk : 2 ≤ k) : Set ℝ := {t | inMaximal hf hdec hν hk t}
