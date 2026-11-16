/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ClayStatements.lean, line 527

/-!
# manuscript.lean.conditional_regularity_nonvacuous_at_zero

Machine-checked Lean 4 module.
-/

public theorem conditional_regularity_nonvacuous_at_zero (ν : ℝ) (hν : 0 < ν) :
    ∃ (u : TimeDependentVelocity),
      (∀ t ≥ (0 : ℝ), ConditionalRegularity.IsSmooth (u t)) ∧
      (u 0 = 0) ∧
      (∀ t ≥ (0 : ℝ), ConditionalRegularity.satisfies_NavierStokes u ν) ∧
      (∀ t ≥ (0 : ℝ), ConditionalRegularity.vorticity_sup_norm (vorticity (u t)) ≥ 0) ∧
      (∀ v : TimeDependentVelocity,
        (∀ t ≥ (0 : ℝ), ConditionalRegularity.IsSmooth (v t)) →
        v 0 = 0 →
        (∀ t ≥ (0 : ℝ), ConditionalRegularity.satisfies_NavierStokes v ν) →
        ∀ t ≥ (0 : ℝ), v t = u t) := ...
