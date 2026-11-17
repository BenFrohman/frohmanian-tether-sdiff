/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- Scratch/KatoMaximal.lean, lines 1793-1796

/-!
# papers.local-kato-theory.lean.T6

Verbatim excerpt (statement only) of the kernel-checked source file named above.
-/

theorem energyInequality_physicalMaximal (hdiv : ∀ x, div u₀ x = 0) {T : ℝ}
    (hS : Ico (0 : ℝ) T ⊆ Smax hf hdec hν (by norm_num : 2 ≤ 2)) :
    ∀ t ∈ Ico (0 : ℝ) T,
      ∫⁻ x, ‖physicalMaximal hf hdec hν t x‖ₑ ^ 2 ≤ ∫⁻ x, ‖u₀ x‖ₑ ^ 2
