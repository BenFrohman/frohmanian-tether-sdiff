-- FrohmanianTether/TetherDefinitionAudit.lean, line 150
@[expose] public def escapePath : TimeDependentVelocity := fun t y =>
  (if 0 < t then t ^ 2 else 0) • abcProfile (t⁻¹ ^ 3) 1 0 0 y
