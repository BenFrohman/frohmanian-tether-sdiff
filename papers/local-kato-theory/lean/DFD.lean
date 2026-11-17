@[expose] public def FeffermanDecay (u₀ : VelocityField) : Prop :=
  ∀ (k : ℕ) (α : Fin k → Fin 3) (K : ℝ), ∃ C : ℝ, ∀ x : T3,
    ‖iteratedFDeriv ℝ k u₀ x (fun j => EuclideanSpace.single (α j) (1 : ℝ))‖ ≤
      C * (1 + ‖x‖) ^ (-K)
