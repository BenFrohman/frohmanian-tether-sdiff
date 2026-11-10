-- FrohmanianTether/TetherWeightProof.lean, line 49
@[expose] public def projCoef (ω : CoadjointOrbit) (v : T3 → EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (∫ y, pairing (v y) (velocity_from_vorticity ω y) ∂NavierStokes3D.volume) /
    (∫ y, ‖velocity_from_vorticity ω y‖ ^ 2 ∂NavierStokes3D.volume)
