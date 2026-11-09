-- FrohmanianTether/SymplecticTether.lean, line 974
@[expose] public def TetherIntegralPreserved (SDiff : Type*) [Group SDiff]
    [MulAction SDiff CoadjointOrbit] : Prop :=
  ∀ (g : SDiff) (F G : Functional) (ω : CoadjointOrbit),
    (∫ x,
      inner ℝ
        (Pi_u (velocity_from_vorticity (CoadjointAction g ω))
          (FunctionalDerivative F (CoadjointAction g ω)) x)
        (Pi_u (velocity_from_vorticity (CoadjointAction g ω))
          (FunctionalDerivative G (CoadjointAction g ω)) x) ∂volume) =
    ∫ x,
      inner ℝ
        (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x)
        (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative G ω) x) ∂volume
