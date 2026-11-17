/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- Scratch/KatoMaximal.lean, lines 1626-1633

/-!
# papers.local-kato-theory.lean.T5

Verbatim excerpt (statement only) of the kernel-checked source file named above.
-/

theorem momentum_physicalMaximal (hdiv : ∀ x, div u₀ x = 0) {T : ℝ}
    (hS : Ico (0 : ℝ) T ⊆ Smax hf hdec hν (by norm_num : 2 ≤ 2))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (x : T3) :
    derivWithin (fun s => physicalMaximal hf hdec hν s x) (Ici 0) t +
        convective (physicalMaximal hf hdec hν t)
          (physicalMaximal hf hdec hν t) x +
        pressureGradient (presMaximal hf hdec hν t) x =
      ν • laplacian (physicalMaximal hf hdec hν t) x + 0
