/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
public theorem library_huniq_unsatisfiable_at_zero (ν : ℝ) (w : KatoLocalWitness 0 ν) :
    ¬ (∀ (T' : ℝ) (v : TimeDependentVelocity) (q : TimeDependentPressure),
      T' ∈ existenceTimes 0 ν → v 0 = 0 → NS_PDE v q ν →
      (∀ t ∈ Set.Icc (0 : ℝ) T', ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      ∀ t ∈ Set.Icc (0 : ℝ) T', w.u t = v t) := ...
