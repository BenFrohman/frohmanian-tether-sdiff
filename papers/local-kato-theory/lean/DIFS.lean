/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- Scratch/RepairedTetherRate.lean, lines 66-75

/-!
# papers.local-kato-theory.lean.DIFS

Verbatim excerpt (statement only) of the kernel-checked source file named above.
-/

@[expose] public def IsFeffermanSolutionOn (ν T : ℝ) (u₀ : VelocityField)
    (u : TimeDependentVelocity) (p : TimeDependentPressure) : Prop :=
  ContDiffOn ℝ ∞ (fun q : T3 × ℝ => u q.2 q.1) (Set.univ ×ˢ Set.Ico (0 : ℝ) T) ∧
  ContDiffOn ℝ ∞ (fun q : T3 × ℝ => p q.2 q.1) (Set.univ ×ˢ Set.Ico (0 : ℝ) T) ∧
  (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : T3,
    derivWithin (fun s => u s x) (Set.Ici 0) t + convective (u t) (u t) x +
        pressureGradient (p t) x = ν • laplacian (u t) x + 0 ∧
      div (u t) x = 0) ∧
  (∀ x : T3, u 0 x = u₀ x) ∧
  (∀ t ∈ Set.Ico (0 : ℝ) T, ∫⁻ x, ‖u t x‖ₑ ^ 2 ≤ ∫⁻ x, ‖u₀ x‖ₑ ^ 2)
