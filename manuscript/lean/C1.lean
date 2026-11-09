-- FrohmanianTether/SymplecticTether.lean, line 376
@[expose] public def InvariantUnderCoadjointAction (SDiff : Type*) [Group SDiff]
    [MulAction SDiff CoadjointOrbit] (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  -- (C1): The correction B is invariant under the coadjoint action of SDiff(T³).
  -- For all volume-preserving g, the value of the correction is unchanged when the vorticity
  -- and the test functionals are transformed by the coadjoint action.
  ∀ (g : SDiff) (F G : Functional) (ω : CoadjointOrbit),
    B (CoadjointAction g ω) F G = B ω F G
