-- FrohmanianTether/NS_Equations.lean, line 2149
@[expose] public def navier_stokes_eq (u : TimeDependentVelocity) (p : TimeDependentPressure)
    (ν : ℝ) : Prop :=
  ∀ t ≥ (0 : ℝ), ∀ x : T3,
    time_deriv u t x + convective (u t) (u t) x + pressureGradient (p t) x =
        ν • laplacian (u t) x ∧
      div (u t) x = 0
