/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- Scratch/RepairedTetherRate.lean, lines 84-91

/-!
# papers.local-kato-theory.lean.DRate

Verbatim excerpt (statement only) of the kernel-checked source file named above.
-/

@[expose] public def FrohmanianTetherRateSmooth (u₀ : VelocityField) (ν : ℝ) : Prop :=
  ∃ C kap : ℝ, 0 < C ∧ 0 < kap ∧
    ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsFeffermanSolutionOn ν T u₀ u p →
        ContinuousOn (Mω u) (Set.Ico (0 : ℝ) T) ∧
        (∀ s ∈ Set.Ico (0 : ℝ) T, ∃ d : ℝ,
          HasDerivWithinAt (Mω u) d (Set.Ici s) s ∧ d ≤ C * Mω u s ^ 2 - kap * Mω u s ^ 3) ∧
        (∀ t ∈ Set.Ico (0 : ℝ) T, BddAbove (Set.range fun x => ‖vorticity (u t) x‖))
