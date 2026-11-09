-- FrohmanianTether/KineticEnergyDerivative.lean, line 295
theorem not_forall_functionalDerivative_kineticEnergy_eq_velocity :
    ¬ ∀ ω : CoadjointOrbit,
      FunctionalDerivative KineticEnergyHamiltonian ω = velocity_from_vorticity ω := ...
