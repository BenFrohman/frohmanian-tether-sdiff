-- FrohmanianTether/SymplecticTether.lean, line 222
@[expose] public def InvariantUnderCoadjointAction (SDiff : Type*) [Group SDiff]
    [MulAction SDiff CoadjointOrbit] (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  -- (C1): The correction B is invariant under the coadjoint action of SDiff(T³).
  -- For all g, the value of the correction is unchanged when the vorticity is transformed by
  -- the coadjoint action; the test functionals F, G are NOT transformed.
  ∀ (g : SDiff) (F G : Functional) (ω : CoadjointOrbit),
    B (CoadjointAction g ω) F G = B ω F G
