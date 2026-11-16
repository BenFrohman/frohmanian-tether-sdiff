/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/KineticEnergyDerivative.lean, line 328

/-!
# manuscript.lean.not_unique_velocity_representative

Machine-checked Lean 4 module.
-/

theorem not_unique_velocity_representative (ω : CoadjointOrbit) :
    ¬ (IsGateauxRepresentative KineticEnergyHamiltonian ω (velocity_from_vorticity ω) ∧
      ∀ dH, IsGateauxRepresentative KineticEnergyHamiltonian ω dH →
        dH = velocity_from_vorticity ω) := ...
