-- FrohmanianTether/TetherEquivariantC1.lean, line 118
@[expose] public def l2Translate (h : T3) : L2Field →ₗᵢ[ℝ] L2Field :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x : T3 => x - h) (mp_sub h)
