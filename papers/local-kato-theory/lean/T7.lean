/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- Scratch/KatoMaximal.lean, lines 1193-1195

/-!
# papers.local-kato-theory.lean.T7

Verbatim excerpt (statement only) of the kernel-checked source file named above.
-/

theorem continuousOn_hsSq_physicalMaximal {k : ℕ} (hk : 2 ≤ k) :
    ContinuousOn (fun t => hsSq 3 (physicalMaximal hf hdec hν t))
      (Smax hf hdec hν hk)
