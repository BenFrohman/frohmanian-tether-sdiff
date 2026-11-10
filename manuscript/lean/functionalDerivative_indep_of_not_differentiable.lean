-- FrohmanianTether/ArnoldGeometric.lean, line 407
public theorem functionalDerivative_indep_of_not_differentiable
    {ω : CoadjointOrbit} (hω : ¬ ∀ i x, DifferentiableAt ℝ (fun y => ω.val y i) x)
    (F G : CoadjointOrbit → ℝ) :
    FunctionalDerivative F ω = FunctionalDerivative G ω := ...
