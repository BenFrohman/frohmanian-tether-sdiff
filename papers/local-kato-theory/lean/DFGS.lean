@[expose] public def FeffermanGlobalSolution (ν : ℝ) (u₀ : VelocityField)
    (u : TimeDependentVelocity) (p : TimeDependentPressure) : Prop :=
  ContDiffOn ℝ ∞ (fun q : T3 × ℝ => u q.2 q.1) (Set.univ ×ˢ Set.Ici (0 : ℝ)) ∧
  ContDiffOn ℝ ∞ (fun q : T3 × ℝ => p q.2 q.1) (Set.univ ×ˢ Set.Ici (0 : ℝ)) ∧
  ClayStatements.navier_stokes_eq_Ici u p ν (fun _ _ => 0) ∧
  (∀ x : T3, u 0 x = u₀ x) ∧
  ∃ C : ℝ, ∀ t ≥ (0 : ℝ), ∫⁻ x, ‖u t x‖ₑ ^ 2 < ENNReal.ofReal C
