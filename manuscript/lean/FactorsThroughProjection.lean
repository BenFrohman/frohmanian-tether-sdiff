-- FrohmanianTether/Uniqueness.lean, line 399
@[expose] public def FactorsThroughProjection
    (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  ∀ ω : CoadjointOrbit, ∃ Q : (T3 → EuclideanSpace ℝ (Fin 3)) → (T3 → EuclideanSpace ℝ (Fin 3)) → ℝ,
    (∀ a b, Q a b = Q b a) ∧
    ∀ F G : Functional, B ω F G =
      Q (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω))
        (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative G ω))
