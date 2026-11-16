/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherDefinitionAudit.lean, line 150

/-!
# manuscript.lean.escapePath

Machine-checked Lean 4 module.
-/

@[expose] public def escapePath : TimeDependentVelocity := fun t y =>
  (if 0 < t then t ^ 2 else 0) • abcProfile (t⁻¹ ^ 3) 1 0 0 y
