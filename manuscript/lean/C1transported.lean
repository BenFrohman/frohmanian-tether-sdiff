/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherEquivariantC1.lean, line 52

/-!
# manuscript.lean.C1transported

Machine-checked Lean 4 module.
-/

@[expose] public def InvariantUnderTransportedCoadjointAction (SDiff : Type*) [Group SDiff]
    [MulAction SDiff CoadjointOrbit] (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  ∀ (g : SDiff) (F G : Functional) (ω : CoadjointOrbit),
    B (CoadjointAction g ω) (fun η => F (g⁻¹ • η)) (fun η => G (g⁻¹ • η)) = B ω F G
