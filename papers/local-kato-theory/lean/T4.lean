/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- Scratch/KatoMaximal.lean, lines 1809-1812

/-!
# papers.local-kato-theory.lean.T4

Verbatim excerpt (statement only) of the kernel-checked source file named above.
-/

theorem isFeffermanSolutionOn_physicalMaximal (hdiv : ∀ x, div u₀ x = 0)
    {T : ℝ} (hS : Ico (0 : ℝ) T ⊆ Smax hf hdec hν (by norm_num : 2 ≤ 2)) :
    IsFeffermanSolutionOn ν T u₀
      (physicalMaximal hf hdec hν) (presMaximal hf hdec hν)
