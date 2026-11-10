-- FrohmanianTether/ExplicitFlows.lean, line 313
@[expose] public def shearProfile (k a : ℝ) : VelocityField :=
  trigField k (shearα a) 0 (fun _ => 2) (fun _ => 2)
