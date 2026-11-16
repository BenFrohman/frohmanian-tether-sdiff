/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/KineticEnergyDerivative.lean, line 303

/-!
# manuscript.lean.not_unique_isGateauxRepresentative

Machine-checked Lean 4 module.
-/

theorem not_unique_isGateauxRepresentative (F : CoadjointOrbit → ℝ) (ω : CoadjointOrbit)
    (d : T3 → EuclideanSpace ℝ (Fin 3)) (hd : IsGateauxRepresentative F ω d) :
    ∃ d', IsGateauxRepresentative F ω d' ∧ d' ≠ d := ...
