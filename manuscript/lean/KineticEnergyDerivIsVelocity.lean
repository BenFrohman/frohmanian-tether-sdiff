-- FrohmanianTether/PlanSteps.lean, line 65
def KineticEnergyDerivIsVelocity : Prop :=
  ∀ ω : CoadjointOrbit, FunctionalDerivative KineticEnergyHamiltonian ω = velocity_from_vorticity ω
