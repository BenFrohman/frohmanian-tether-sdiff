/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/NS_Equations.lean, line 2293

/-!
# manuscript.lean.NS_PDE_On

Machine-checked Lean 4 module.
-/

@[expose] public def NS_PDE_On (u : TimeDependentVelocity) (p : TimeDependentPressure) (ν T : ℝ) :
    Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : T3,
    time_deriv u t x + convective (u t) (u t) x + pressureGradient (p t) x =
        ν • laplacian (u t) x ∧
      div (u t) x = 0
