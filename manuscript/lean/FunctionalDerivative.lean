-- FrohmanianTether/ArnoldGeometric.lean, line 313
public noncomputable def FunctionalDerivative (F : CoadjointOrbit → ℝ)
    (ω : CoadjointOrbit) : T3 → EuclideanSpace ℝ (Fin 3) :=
  if h : ∃ δ, IsGateauxRepresentative F ω δ then Classical.choose h else 0
