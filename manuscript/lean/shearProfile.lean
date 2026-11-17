/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 313

/-!
# manuscript.lean.shearProfile

Machine-checked Lean 4 module.
-/

@[expose] public def shearProfile (k a : ℝ) : VelocityField :=
  trigField k (shearα a) 0 (fun _ => 2) (fun _ => 2)
