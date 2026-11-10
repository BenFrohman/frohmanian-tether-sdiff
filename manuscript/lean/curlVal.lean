-- FrohmanianTether/TestFieldFamily.lean, line 38
@[expose] public def curlVal (H : T3 → ℝ) (y : T3) : EuclideanSpace ℝ (Fin 3) :=
  pd H 1 y • eb 0 - pd H 0 y • eb 1
