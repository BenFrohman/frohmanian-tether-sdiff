-- FrohmanianTether/KineticEnergyDerivative.lean, line 328
theorem not_unique_velocity_representative (ω : CoadjointOrbit) :
    ¬ (IsGateauxRepresentative KineticEnergyHamiltonian ω (velocity_from_vorticity ω) ∧
      ∀ dH, IsGateauxRepresentative KineticEnergyHamiltonian ω dH →
        dH = velocity_from_vorticity ω) := ...
