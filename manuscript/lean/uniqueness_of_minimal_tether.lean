-- FrohmanianTether/Uniqueness.lean, line 652
public theorem uniqueness_of_minimal_tether
    (SDiff : Type*) [Group SDiff] [MulAction SDiff CoadjointOrbit]
    (_hyp : SDiffActionHyp SDiff)
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (h_sym : ∀ ω F G, B ω F G = B ω G F)
    (hC1 : InvariantUnderCoadjointAction SDiff B)
    (hC2 : DegenerateWRTKineticEnergy B)
    (hC3 : ProducesControllableNegativeFeedback B)
    (h_sat : SaturatesTetherQuadratic B)
    (h_polarB : PolarizesOnDifferentiable B) :
    ∀ (ω : CoadjointOrbit) (F G : Functional), (∃ g, IsFunctionalGradient F ω g) →
      (∃ g, IsFunctionalGradient G ω g) → B ω F G = TetherKernel ω F G := ...
