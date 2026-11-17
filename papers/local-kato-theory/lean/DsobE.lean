/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- Scratch/R3BKMContinuation.lean, lines 44-46

/-!
# papers.local-kato-theory.lean.DsobE

Verbatim excerpt (statement only) of the kernel-checked source file named above.
-/

def sobolevEnergy (m : ℕ) (f : VelocityField) : ENNReal :=
  ∑ k ∈ Finset.range (m + 1), ∑ α : Fin k → Fin 3,
    ∫⁻ x, ‖iteratedFDeriv ℝ k f x (fun j => EuclideanSpace.single (α j) (1 : ℝ))‖ₑ ^ 2
