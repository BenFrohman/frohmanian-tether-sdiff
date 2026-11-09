/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
public theorem tetherKernel_degenerates_on_kinetic_energy
    (F : Functional) (ω : CoadjointOrbit)
    (hδH : FunctionalDerivative KineticEnergyHamiltonian ω = velocity_from_vorticity ω)
    (hdiv : ∀ x, div (velocity_from_vorticity ω) x = 0)
    (hInt : Integrable (fun y => ‖velocity_from_vorticity ω y‖ ^ 2)) :
    TetherKernel ω F KineticEnergyHamiltonian = 0 := ...
