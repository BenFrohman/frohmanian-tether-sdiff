-- FrohmanianTether/TetherEquivariantC1.lean, line 155
public theorem isFunctionalGradient_translate (h : T3) {F : CoadjointOrbit → ℝ}
    {ω : CoadjointOrbit} {g : L2Field} (hg : IsFunctionalGradient F ω g) :
    IsFunctionalGradient (fun η => F ((translate h)⁻¹ • η)) (translate h • ω)
      (l2Translate h g) := ...
