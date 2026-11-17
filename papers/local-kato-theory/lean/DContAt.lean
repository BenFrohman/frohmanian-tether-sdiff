/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- Scratch/RepairedTetherRate.lean, lines 98-102

/-!
# papers.local-kato-theory.lean.DContAt

Verbatim excerpt (statement only) of the kernel-checked source file named above.
-/

@[expose] public def R3BKMContinuationAt (ν : ℝ) (u₀ : VelocityField) : Prop :=
  (∃ Y : ℝ, ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsFeffermanSolutionOn ν T u₀ u p → ∀ t ∈ Set.Ico (0 : ℝ) T,
        BddAbove (Set.range fun x => ‖vorticity (u t) x‖) ∧ Mω u t ≤ Y) →
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure), FeffermanGlobalSolution ν u₀ u p
