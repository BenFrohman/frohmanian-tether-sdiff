-- FrohmanianTether/ExplicitFlows.lean, line 184
@[expose] public def decay (c t : ℝ) : ℝ := if 0 ≤ t then Real.exp (c * t) else 1 + c * t
