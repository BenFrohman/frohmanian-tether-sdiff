-- FrohmanianTether/ExplicitFlows.lean, line 377
@[expose] public def abcProfile (k A B C : ℝ) : VelocityField :=
  trigField k (abcα A B C) (abcβ A B C) abcj abcl
