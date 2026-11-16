/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/SymplecticTether.lean, line 623

/-!
# manuscript.lean.tetherKernel_C2_of_no_gateaux

Machine-checked Lean 4 module.
-/

public theorem tetherKernel_C2_of_no_gateaux
    (ω : CoadjointOrbit)
    (h : ¬ ∃ dH, IsFunctionalGradient KineticEnergyHamiltonian ω dH)
    (F : Functional) :
    TetherKernel ω F KineticEnergyHamiltonian = 0 := ...
