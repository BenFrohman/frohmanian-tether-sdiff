-- FrohmanianTether/ExplicitFlows.lean, line 49
@[expose] public def tp (k α β : ℝ) (j l : Fin 3) (y : T3) : ℝ :=
  α * Real.sin (k * y j) + β * Real.cos (k * y l)
