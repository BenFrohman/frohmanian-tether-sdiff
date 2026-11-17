/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- Scratch/KatoMaximal.lean, lines 561-562

/-!
# papers.local-kato-theory.lean.DinMax

Verbatim excerpt (statement only) of the kernel-checked source file named above.
-/

def inMaximal {k : ℕ} (hk : 2 ≤ k) (t : ℝ) : Prop :=
  0 ≤ t ∧ ∃ n : ℕ, t ≤ (iteratePath hf hdec hν hk n).t
