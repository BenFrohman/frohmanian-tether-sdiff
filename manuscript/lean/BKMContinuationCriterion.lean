/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/NS_Equations.lean, line 3134

/-!
# manuscript.lean.BKMContinuationCriterion

Machine-checked Lean 4 module.
-/

@[expose] public def BKMContinuationCriterion (u : TimeDependentVelocity) (ν : ℝ) : Prop :=
  ∀ T : ℝ, Tstar (u 0) ν = (T : EReal) →
    ¬ IntegrableOn (fun t => vorticity_sup_norm (vorticity (u t))) (Set.Icc 0 T)
