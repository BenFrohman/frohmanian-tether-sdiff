-- FrohmanianTether/NS_Equations.lean, line 2302
@[expose] public def IsPhysicalNSSolutionOn (u : TimeDependentVelocity) (T : ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : T3, DifferentiableAt ℝ (fun s => u s x) t) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) T, Continuous (u t)) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) T, Integrable (fun x : T3 => ‖u t x‖ ^ 2)) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) T, (∫ x, ‖u t x‖ ^ 2 ∂volume) ≤ ∫ x, ‖u 0 x‖ ^ 2 ∂volume) ∧
  (∃ v₀ : VelocityField, ∀ t ≤ (0 : ℝ), u t = u 0 + t • v₀)
