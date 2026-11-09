-- FrohmanianTether/Uniqueness.lean, line 303
public def SaturatesTetherQuadratic
    (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  ∀ (F : Functional) (ω : CoadjointOrbit), B ω F F = TetherKernel ω F F
