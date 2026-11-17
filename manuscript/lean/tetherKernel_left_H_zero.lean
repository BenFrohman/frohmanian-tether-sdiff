/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/Combined.lean, line 52

/-!
# manuscript.lean.tetherKernel_left_H_zero

Machine-checked Lean 4 module.
-/

theorem tetherKernel_left_H_zero (hC2 : DegenerateWRTKineticEnergy TetherKernel)
    (ω : CoadjointOrbit) (M : Functional) :
    TetherKernel ω KineticEnergyHamiltonian M = 0 ∧ TetherKernel ω M KineticEnergyHamiltonian = 0 := ...
