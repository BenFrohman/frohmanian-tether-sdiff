/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
-- NS_Millennium_Proof/Modules/SymplecticTether.lean
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

public theorem tether_coadjoint_invariance (SDiff : Type*) [Group SDiff]
    [MulAction SDiff CoadjointOrbit] (hyp : SDiffActionHyp SDiff)
    (h_density : TetherIntegralPreserved SDiff)
    (g : SDiff) (F G : Functional) (ω : CoadjointOrbit) :
    TetherKernel (CoadjointAction g ω) F G = TetherKernel ω F G := by
  unfold TetherKernel
  rw [hyp.enstrophy_invariant g ω, h_density g F G ω]
