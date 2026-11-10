-- FrohmanianTether/TetherEquivariantC1.lean, line 181
public theorem functionalDerivative_translate (h : T3) (F : CoadjointOrbit → ℝ)
    (ω : CoadjointOrbit) :
    FunctionalDerivative (fun η => F ((translate h)⁻¹ • η)) (translate h • ω)
      =ᵐ[MeasureTheory.volume] fun x => FunctionalDerivative F ω (x - h) := ...
