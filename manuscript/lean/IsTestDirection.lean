-- FrohmanianTether/ArnoldGeometric.lean, line 309
@[expose] public def IsTestDirection (ε : CoadjointOrbit) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) ε.val ∧ HasCompactSupport ε.val
