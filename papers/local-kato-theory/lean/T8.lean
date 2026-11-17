/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- Scratch/KatoMaximal.lean, lines 1229-1234

/-!
# papers.local-kato-theory.lean.T8

Verbatim excerpt (statement only) of the kernel-checked source file named above.
-/

theorem hsSq_blowup_alternative {k : ℕ} (hk : 2 ≤ k) :
    Smax hf hdec hν hk = Ici (0 : ℝ) ∨
      ∃ Tstar : ℝ, 0 < Tstar ∧
        Smax hf hdec hν hk = Ico 0 Tstar ∧
        ∀ B : ℝ, ∃ t, t ∈ Ico (0 : ℝ) Tstar ∧
          B < hsSq 3 (physicalMaximal hf hdec hν t)
