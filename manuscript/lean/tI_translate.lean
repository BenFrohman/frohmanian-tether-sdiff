-- FrohmanianTether/TetherEquivariantC1.lean, line 225
public theorem tI_translate (h : T3) (ω : CoadjointOrbit)
    {a b a' b' : T3 → EuclideanSpace ℝ (Fin 3)}
    (ha : a' =ᵐ[MeasureTheory.volume] fun x => a (x - h))
    (hb : b' =ᵐ[MeasureTheory.volume] fun x => b (x - h)) :
    tI (translate h • ω) a' b' = tI ω a b := ...
