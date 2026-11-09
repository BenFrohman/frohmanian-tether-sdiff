-- FrohmanianTether/SymplecticTether.lean, line 1030
public theorem tetherKernel_C2_of_no_gateaux
    (ω : CoadjointOrbit)
    (h : ¬ ∃ dH, IsGateauxRepresentative KineticEnergyHamiltonian ω dH)
    (F : Functional) :
    TetherKernel ω F KineticEnergyHamiltonian = 0 := ...
