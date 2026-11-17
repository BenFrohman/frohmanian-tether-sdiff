/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetheredLyapunov.lean, line 1427

/-!
# manuscript.lean.KatoUniquenessOnExistenceTimes

Machine-checked Lean 4 module.
-/

@[expose] public def KatoUniquenessOnExistenceTimes (u₀ : VelocityField) (ν : ℝ)
    (w : KatoLocalWitness u₀ ν) : Prop :=
  ∀ (T' : ℝ) (v : TimeDependentVelocity) (q : TimeDependentPressure),
    T' ∈ existenceTimes u₀ ν → v 0 = u₀ → NS_PDE_On v q ν T' →
    (∀ t ∈ Set.Icc (0 : ℝ) T', ContDiff ℝ (⊤ : ℕ∞) (v t)) →
    IsPhysicalNSSolutionOn v T' →
    ∀ t ∈ Set.Icc (0 : ℝ) T', w.u t = v t
