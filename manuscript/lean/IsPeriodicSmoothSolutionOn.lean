-- FrohmanianTether/ClayStatements.lean, line 529
@[expose] public def IsPeriodicSmoothSolutionOn (ν T : ℝ) (u₀ : VelocityField)
    (u : TimeDependentVelocity) (p : TimeDependentPressure) : Prop :=
  ContDiffOn ℝ ∞ (fun q : ℝ × T3 => u q.1 q.2) (Set.Ico (0 : ℝ) T ×ˢ Set.univ) ∧
  ContDiffOn ℝ ∞ (fun q : ℝ × T3 => p q.1 q.2) (Set.Ico (0 : ℝ) T ×ˢ Set.univ) ∧
  (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : T3,
    derivWithin (fun s => u s x) (Set.Ici 0) t + convective (u t) (u t) x +
        pressureGradient (p t) x = ν • laplacian (u t) x ∧ div (u t) x = 0) ∧
  u 0 = u₀ ∧
  ∀ t ∈ Set.Ico (0 : ℝ) T, IsZ3Periodic (u t) ∧ IsZ3Periodic (p t)
