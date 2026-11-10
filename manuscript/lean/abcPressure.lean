-- FrohmanianTether/ExplicitFlows.lean, line 403
@[expose] public def abcPressure (ν k A B C : ℝ) : TimeDependentPressure :=
  flowPressure ν k (abcPressure₀ k A B C)
