/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 317

/-!
# manuscript.lean.shearFlow

Machine-checked Lean 4 module.
-/

@[expose] public def shearFlow (ν k a : ℝ) : TimeDependentVelocity :=
  flow ν k (shearα a) 0 (fun _ => 2) (fun _ => 2)
