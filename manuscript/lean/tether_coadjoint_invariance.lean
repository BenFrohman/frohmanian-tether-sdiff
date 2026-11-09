-- FrohmanianTether/SymplecticTether.lean, line 990
public theorem tether_coadjoint_invariance (SDiff : Type*) [Group SDiff]
    [MulAction SDiff CoadjointOrbit] (hyp : SDiffActionHyp SDiff)
    (h_density : TetherIntegralPreserved SDiff)
    (g : SDiff) (F G : Functional) (ω : CoadjointOrbit) :
    TetherKernel (CoadjointAction g ω) F G = TetherKernel ω F G := ...
