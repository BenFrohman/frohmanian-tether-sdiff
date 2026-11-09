-- FrohmanianTether/ForMathlib/Projection.lean, line 35
@[expose] public noncomputable def Pi_u (u v : VelocityField) : VelocityField :=
  fun x => v x - (
    (∫ y, pairing (v y) (u y) ∂volume) /
    (∫ y, ‖u y‖ ^ 2 ∂volume)
  ) • u x
