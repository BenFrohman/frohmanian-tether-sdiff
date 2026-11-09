-- FrohmanianTether/Combined.lean, line 58
theorem left_H_zero_of_C2_symm
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (h_sym : ∀ ω F G, B ω F G = B ω G F) (hC2 : DegenerateWRTKineticEnergy B)
    (ω : CoadjointOrbit) (M : Functional) :
    B ω KineticEnergyHamiltonian M = 0 := ...
