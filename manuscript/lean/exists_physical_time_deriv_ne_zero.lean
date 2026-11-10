-- FrohmanianTether/PhysicalSolutionSanity.lean, line 144
public theorem exists_physical_time_deriv_ne_zero :
    ∃ u : TimeDependentVelocity, IsPhysicalNSSolution u ∧
      ∃ x : T3, deriv (fun s => u s x) 0 ≠ 0 := ...
