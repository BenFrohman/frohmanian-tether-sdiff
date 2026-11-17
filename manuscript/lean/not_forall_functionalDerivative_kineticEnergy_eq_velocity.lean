/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/KineticEnergyDerivative.lean, line 286

/-!
# manuscript.lean.not_forall_functionalDerivative_kineticEnergy_eq_velocity

Machine-checked Lean 4 module.
-/

theorem not_forall_functionalDerivative_kineticEnergy_eq_velocity :
    ¬ ∀ ω : CoadjointOrbit,
      FunctionalDerivative KineticEnergyHamiltonian ω = velocity_from_vorticity ω := ...
