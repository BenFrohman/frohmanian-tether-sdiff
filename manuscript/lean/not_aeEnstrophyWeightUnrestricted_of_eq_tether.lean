-- FrohmanianTether/TetherWeight.lean, line 237
public theorem not_aeEnstrophyWeightUnrestricted_of_eq_tether
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (hB : ∀ ω F G, B ω F G = TetherKernel ω F G) : ¬ AEEnstrophyWeightUnrestricted B := ...
