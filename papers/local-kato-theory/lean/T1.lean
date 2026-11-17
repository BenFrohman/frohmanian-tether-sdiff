/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- Scratch/KatoMaximal.lean, lines 2103-2104

/-!
# papers.local-kato-theory.lean.T1

Verbatim excerpt (statement only) of the kernel-checked source file named above.
-/

theorem katoMaximalSolution_of_feffermanDecay (hdiv : ∀ x, div u₀ x = 0) :
    KatoMaximalSolution ν u₀
