-- FrohmanianTether/PhysicalSolutionSanity.lean, line 157
public theorem not_forall_physical_time_deriv_zero :
    ¬ ∀ u : TimeDependentVelocity, IsPhysicalNSSolution u →
      ∀ x : T3, deriv (fun s => u s x) 0 = 0 := ...
