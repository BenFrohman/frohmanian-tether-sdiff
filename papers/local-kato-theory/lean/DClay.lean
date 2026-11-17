/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- Scratch/RepairedTetherRate.lean, lines 56-60

/-!
# papers.local-kato-theory.lean.DClay

Verbatim excerpt (statement only) of the kernel-checked source file named above.
-/

@[expose] public def Clay_A_Fefferman : Prop :=
  ∀ (ν : ℝ) (u₀ : VelocityField),
    0 < ν → ContDiff ℝ ∞ u₀ → (∀ x, div u₀ x = 0) → FeffermanDecay u₀ →
      ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
        FeffermanGlobalSolution ν u₀ u p
