-- FrohmanianTether/NS_Equations.lean, line 2259
@[expose] public def IsPhysicalNSSolution (u : TimeDependentVelocity) : Prop :=
  (∀ t ≥ (0 : ℝ), ∀ x : T3, DifferentiableAt ℝ (fun s => u s x) t) ∧
  (∀ t ≥ (0 : ℝ), Continuous (u t)) ∧
  (∀ t ≥ (0 : ℝ), Integrable (fun x : T3 => ‖u t x‖ ^ 2)) ∧
  (∀ t ≥ (0 : ℝ), (∫ x, ‖u t x‖ ^ 2 ∂volume) ≤ ∫ x, ‖u 0 x‖ ^ 2 ∂volume) ∧
  (∀ t ≤ (0 : ℝ), u t = u 0)
