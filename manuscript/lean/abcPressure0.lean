-- FrohmanianTether/ExplicitFlows.lean, line 393
@[expose] public def abcPressure₀ (k A B C : ℝ) : PressureField := fun y =>
  -((abcProfile k A B C y 0) ^ 2 + (abcProfile k A B C y 1) ^ 2 +
    (abcProfile k A B C y 2) ^ 2) / 2
