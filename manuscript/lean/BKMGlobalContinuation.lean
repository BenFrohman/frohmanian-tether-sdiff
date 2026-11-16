/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetheredLyapunov.lean, line 1590

/-!
# manuscript.lean.BKMGlobalContinuation

Machine-checked Lean 4 module.
-/

@[expose] public def BKMGlobalContinuation (u₀ : VelocityField) (ν : ℝ) : Prop :=
  Nonempty (KatoLocalWitness u₀ ν) → LocalFiniteTimeVorticityBound u₀ ν →
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      u 0 = u₀ ∧ NS_PDE u p ν ∧ (∀ t ≥ (0 : ℝ), ContDiff ℝ (⊤ : ℕ∞) (u t)) ∧
        IsPhysicalNSSolution u
