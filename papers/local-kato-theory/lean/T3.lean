/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- Scratch/KatoMaximal.lean, lines 2036-2039

/-!
# papers.local-kato-theory.lean.T3

Verbatim excerpt (statement only) of the kernel-checked source file named above.
-/

theorem h3IBPVanishingFlux_physicalMaximal (hdiv : ∀ x, div u₀ x = 0)
    {t : ℝ} (ht : inMaximal hf hdec hν (by norm_num : 2 ≤ 2) t) :
    H3IBPVanishingFlux (physicalMaximal hf hdec hν t)
      (presMaximal hf hdec hν t)
