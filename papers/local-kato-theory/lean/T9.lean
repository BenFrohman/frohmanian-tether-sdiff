/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- Scratch/KatoMaximal.lean, lines 1052-1054

/-!
# papers.local-kato-theory.lean.T9

Verbatim excerpt (statement only) of the kernel-checked source file named above.
-/

theorem Smax_eq_Ici_or_Ico {k : ℕ} (hk : 2 ≤ k) :
    Smax hf hdec hν hk = Ici 0 ∨
      ∃ Tstar : ℝ, 0 < Tstar ∧ Smax hf hdec hν hk = Ico 0 Tstar
