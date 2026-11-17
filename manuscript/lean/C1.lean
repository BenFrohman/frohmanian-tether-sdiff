/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/SymplecticTether.lean, line 222

/-!
# manuscript.lean.C1

Machine-checked Lean 4 module.
-/

@[expose] public def InvariantUnderCoadjointAction (SDiff : Type*) [Group SDiff]
    [MulAction SDiff CoadjointOrbit] (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  -- (C1): The correction B is invariant under the coadjoint action of SDiff(T³).
  -- For all g, the value of the correction is unchanged when the vorticity is transformed by
  -- the coadjoint action; the test functionals F, G are NOT transformed.
  ∀ (g : SDiff) (F G : Functional) (ω : CoadjointOrbit),
    B (CoadjointAction g ω) F G = B ω F G
