-- FrohmanianTether/ArnoldGeometric.lean, line 173
public structure CoadjointOrbit where
  val : T3 → EuclideanSpace ℝ (Fin 3)
  property : ∀ x, NavierStokes3D.div val x = 0
