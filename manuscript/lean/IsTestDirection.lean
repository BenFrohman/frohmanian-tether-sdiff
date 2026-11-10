-- FrohmanianTether/ArnoldGeometric.lean, line 315
@[expose] public def IsTestDirection (ε : CoadjointOrbit) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) ε.val ∧ HasCompactSupport ε.val
