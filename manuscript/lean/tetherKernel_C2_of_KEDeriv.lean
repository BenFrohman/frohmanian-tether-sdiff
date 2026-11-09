-- FrohmanianTether/Combined.lean, line 51
theorem tetherKernel_C2_of_KEDeriv
    (hδ : PlanSteps.KineticEnergyDerivIsVelocity)
    (hdiv : ∀ ω x, div (velocity_from_vorticity ω) x = 0)
    (hInt : ∀ ω, Integrable (fun y => ‖velocity_from_vorticity ω y‖ ^ 2)) :
    DegenerateWRTKineticEnergy TetherKernel := ...
