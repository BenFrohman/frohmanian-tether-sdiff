/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherWeightProof.lean, line 49

/-!
# manuscript.lean.projCoef

Machine-checked Lean 4 module.
-/

@[expose] public def projCoef (ω : CoadjointOrbit) (v : T3 → EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (∫ y, pairing (v y) (velocity_from_vorticity ω y) ∂NavierStokes3D.volume) /
    (∫ y, ‖velocity_from_vorticity ω y‖ ^ 2 ∂NavierStokes3D.volume)
