-- FrohmanianTether/ArnoldGeometric.lean, line 343
@[expose] public def IsFunctionalGradient (F : CoadjointOrbit → ℝ) (ω : CoadjointOrbit) (g : L2Field) : Prop :=
  g ∈ DivFreeL2 ∧ ∃ hω : IsRegularVorticity ω, ∀ ε (hε : IsTestDirection ε),
    HasDerivAt (fun t => F (orbitLine ω ε hω hε.regular t)) (inner ℝ g (testToL2 ε hε)) 0
