-- FrohmanianTether/ExplicitFlows.lean, line 130
@[expose] public def trigField (k : ℝ) (α β : Fin 3 → ℝ) (j l : Fin 3 → Fin 3) : VelocityField :=
  fun y => WithLp.toLp 2 (fun i => tp k (α i) (β i) (j i) (l i) y)
