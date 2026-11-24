/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- Scratch/RepairedTetherRate.lean, lines 44-50

/-!
# papers.local-kato-theory.lean.DFGS

Verbatim excerpt (statement only) of the kernel-checked source file named above.
-/

@[expose] public def FeffermanGlobalSolution (ν : ℝ) (u₀ : VelocityField)
    (u : TimeDependentVelocity) (p : TimeDependentPressure) : Prop :=
  ContDiffOn ℝ ∞ (fun q : T3 × ℝ => u q.2 q.1) (Set.univ ×ˢ Set.Ici (0 : ℝ)) ∧
  ContDiffOn ℝ ∞ (fun q : T3 × ℝ => p q.2 q.1) (Set.univ ×ˢ Set.Ici (0 : ℝ)) ∧
  ClayStatements.navier_stokes_eq_Ici u p ν (fun _ _ => 0) ∧
  (∀ x : T3, u 0 x = u₀ x) ∧
  ∃ C : ℝ, ∀ t ≥ (0 : ℝ), ∫⁻ x, ‖u t x‖ₑ ^ 2 < ENNReal.ofReal C
