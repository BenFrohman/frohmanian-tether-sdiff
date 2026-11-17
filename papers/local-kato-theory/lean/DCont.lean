/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- Scratch/RepairedTetherRate.lean, lines 104-106

/-!
# papers.local-kato-theory.lean.DCont

Verbatim excerpt (statement only) of the kernel-checked source file named above.
-/

@[expose] public def R3BKMContinuation (ν : ℝ) : Prop :=
  ∀ u₀ : VelocityField, ContDiff ℝ ∞ u₀ → (∀ x, div u₀ x = 0) → FeffermanDecay u₀ →
    R3BKMContinuationAt ν u₀
