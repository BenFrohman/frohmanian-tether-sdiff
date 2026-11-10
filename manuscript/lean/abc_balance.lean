-- FrohmanianTether/ExplicitFlows.lean, line 437
public theorem abc_balance (k A B C : ℝ) (x : T3) :
    convective (abcProfile k A B C) (abcProfile k A B C) x +
      pressureGradient (abcPressure₀ k A B C) x = 0 := ...
