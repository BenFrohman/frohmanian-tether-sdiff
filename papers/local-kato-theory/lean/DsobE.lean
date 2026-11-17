def sobolevEnergy (m : ℕ) (f : VelocityField) : ENNReal :=
  ∑ k ∈ Finset.range (m + 1), ∑ α : Fin k → Fin 3,
    ∫⁻ x, ‖iteratedFDeriv ℝ k f x (fun j => EuclideanSpace.single (α j) (1 : ℝ))‖ₑ ^ 2
