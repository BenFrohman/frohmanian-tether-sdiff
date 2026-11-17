/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ArnoldGeometric.lean, line 337

/-!
# manuscript.lean.IsFunctionalGradient

Machine-checked Lean 4 module.
-/

@[expose] public def IsFunctionalGradient (F : CoadjointOrbit → ℝ) (ω : CoadjointOrbit) (g : L2Field) : Prop :=
  g ∈ DivFreeL2 ∧ ∃ hω : IsRegularVorticity ω, ∀ ε (hε : IsTestDirection ε),
    HasDerivAt (fun t => F (orbitLine ω ε hω hε.regular t)) (inner ℝ g (testToL2 ε hε)) 0
