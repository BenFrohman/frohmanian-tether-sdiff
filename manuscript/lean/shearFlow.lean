-- FrohmanianTether/ExplicitFlows.lean, line 317
@[expose] public def shearFlow (ν k a : ℝ) : TimeDependentVelocity :=
  flow ν k (shearα a) 0 (fun _ => 2) (fun _ => 2)
