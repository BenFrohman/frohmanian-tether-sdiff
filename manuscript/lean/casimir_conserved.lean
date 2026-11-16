/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/PlanSteps.lean, line 67

/-!
# manuscript.lean.casimir_conserved

Machine-checked Lean 4 module.
-/

theorem casimir_conserved {SDiff : Type*} [Group SDiff] [MulAction SDiff CoadjointOrbit]
    (H : SDiffActionHyp SDiff) (ω : ℝ → CoadjointOrbit) (hω : IsCoadjointMotion SDiff ω)
    (f : ℝ → ℝ) (t : ℝ) : Casimir f (ω t) = Casimir f (ω 0) := ...
