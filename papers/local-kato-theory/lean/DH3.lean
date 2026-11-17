def H3IBPVanishingFlux (u : VelocityField) (p : PressureField) : Prop :=
  ∀ k ∈ Finset.range 4, ∀ α : Fin k → Fin 3, WordIBP u p k α
