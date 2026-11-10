-- FrohmanianTether/SymplecticConstraint.lean, line 718
public theorem nonzero_smooth_ns_solution_exists (ν : ℝ) (c : T3) (hc : c ≠ 0) :
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      u 0 ≠ 0 ∧
      (∀ t ≥ (0 : ℝ), IsSmooth (u t)) ∧
      navier_stokes_eq u p ν := ...
