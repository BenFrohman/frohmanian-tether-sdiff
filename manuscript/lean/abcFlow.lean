-- FrohmanianTether/ExplicitFlows.lean, line 381
@[expose] public def abcFlow (ν k A B C : ℝ) : TimeDependentVelocity :=
  flow ν k (abcα A B C) (abcβ A B C) abcj abcl
