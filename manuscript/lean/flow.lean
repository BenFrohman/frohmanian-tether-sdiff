-- FrohmanianTether/ExplicitFlows.lean, line 233
@[expose] public def flow (ν k : ℝ) (α β : Fin 3 → ℝ) (j l : Fin 3 → Fin 3) :
    TimeDependentVelocity :=
  fun t y => decay (-(ν * k ^ 2)) t • trigField k α β j l y
