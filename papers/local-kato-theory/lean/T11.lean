/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- Scratch/KatoContinuation.lean, lines 49-52

/-!
# papers.local-kato-theory.lean.T11

Verbatim excerpt (statement only) of the kernel-checked source file named above.
-/

theorem clay_A_fefferman_of_rate
    (hrate : ∀ ν > (0 : ℝ), ∀ u₀ : VelocityField, ContDiff ℝ ∞ u₀ →
      (∀ x, div u₀ x = 0) → FeffermanDecay u₀ → FrohmanianTetherRateSmooth u₀ ν) :
    Clay_A_Fefferman
