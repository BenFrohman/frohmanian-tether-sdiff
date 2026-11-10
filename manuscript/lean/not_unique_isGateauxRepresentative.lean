-- FrohmanianTether/KineticEnergyDerivative.lean, line 303
theorem not_unique_isGateauxRepresentative (F : CoadjointOrbit → ℝ) (ω : CoadjointOrbit)
    (d : T3 → EuclideanSpace ℝ (Fin 3)) (hd : IsGateauxRepresentative F ω d) :
    ∃ d', IsGateauxRepresentative F ω d' ∧ d' ≠ d := ...
