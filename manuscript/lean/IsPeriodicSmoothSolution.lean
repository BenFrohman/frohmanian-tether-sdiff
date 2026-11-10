-- FrohmanianTether/ClayStatements.lean, line 247
@[expose] public def IsPeriodicSmoothSolution (ν : ℝ) (u₀ : VelocityField)
    (f : ℝ → T3 → EuclideanSpace ℝ (Fin 3))
    (u : TimeDependentVelocity) (p : TimeDependentPressure) : Prop :=
  ContDiffOn ℝ ∞ (fun q : ℝ × T3 => u q.1 q.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) ∧
  ContDiffOn ℝ ∞ (fun q : ℝ × T3 => p q.1 q.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) ∧
  navier_stokes_eq_Ici u p ν f ∧
  u 0 = u₀ ∧
  ∀ t ≥ (0 : ℝ), IsZ3Periodic (u t) ∧ IsZ3Periodic (p t)
