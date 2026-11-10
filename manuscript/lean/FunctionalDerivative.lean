-- FrohmanianTether/ArnoldGeometric.lean, line 373
@[expose] public noncomputable def FunctionalDerivative (F : CoadjointOrbit → ℝ) (ω : CoadjointOrbit) : T3 → EuclideanSpace ℝ (Fin 3) :=
  if h : ∃ g, IsFunctionalGradient F ω g then ⇑(Classical.choose h) else 0
