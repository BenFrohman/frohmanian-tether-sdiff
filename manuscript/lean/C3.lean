-- FrohmanianTether/SymplecticTether.lean, line 390
@[expose] public def ProducesControllableNegativeFeedback
    (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  ∀ (F : Functional) (ω : CoadjointOrbit),
    B ω F F ≤
      -kappa * Enstrophy ω * ∫ x,
          ‖Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x‖ ^ 2
        ∂volume
