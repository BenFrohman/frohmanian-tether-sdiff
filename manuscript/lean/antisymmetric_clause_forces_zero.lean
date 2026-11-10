-- FrohmanianTether/Uniqueness.lean, line 335
public theorem antisymmetric_clause_forces_zero
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (h_antisym : ∀ ω F G, B ω F G = -B ω G F)
    (h_sat : SaturatesTetherQuadratic B)
    (h_polarB : Polarizes B)
    (h_polarT : Polarizes TetherKernel) :
    ∀ (ω : CoadjointOrbit) (F G : Functional), B ω F G = 0 ∧ TetherKernel ω F G = 0 := ...
