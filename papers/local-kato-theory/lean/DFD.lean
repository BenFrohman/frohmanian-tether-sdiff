/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- Scratch/RepairedTetherRate.lean, lines 33-36

/-!
# papers.local-kato-theory.lean.DFD

Verbatim excerpt (statement only) of the kernel-checked source file named above.
-/

@[expose] public def FeffermanDecay (u₀ : VelocityField) : Prop :=
  ∀ (k : ℕ) (α : Fin k → Fin 3) (K : ℝ), ∃ C : ℝ, ∀ x : T3,
    ‖iteratedFDeriv ℝ k u₀ x (fun j => EuclideanSpace.single (α j) (1 : ℝ))‖ ≤
      C * (1 + ‖x‖) ^ (-K)
