-- FrohmanianTether/ExplicitFlows.lean, line 248
@[expose] public def flowPressure (ν k : ℝ) (p₀ : PressureField) : TimeDependentPressure :=
  fun t y => decay (-(ν * k ^ 2)) t ^ 2 * p₀ y
