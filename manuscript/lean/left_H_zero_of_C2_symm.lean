/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/Combined.lean, line 44

/-!
# manuscript.lean.left_H_zero_of_C2_symm

Machine-checked Lean 4 module.
-/

theorem left_H_zero_of_C2_symm
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (h_sym : ∀ ω F G, B ω F G = B ω G F) (hC2 : DegenerateWRTKineticEnergy B)
    (ω : CoadjointOrbit) (M : Functional) :
    B ω KineticEnergyHamiltonian M = 0 := ...
