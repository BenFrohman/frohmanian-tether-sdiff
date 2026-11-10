-- FrohmanianTether/TetherEquivariantC1.lean, line 52
@[expose] public def InvariantUnderTransportedCoadjointAction (SDiff : Type*) [Group SDiff]
    [MulAction SDiff CoadjointOrbit] (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  ∀ (g : SDiff) (F G : Functional) (ω : CoadjointOrbit),
    B (CoadjointAction g ω) (fun η => F (g⁻¹ • η)) (fun η => G (g⁻¹ • η)) = B ω F G
