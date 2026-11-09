/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
public def SaturatesTetherQuadratic
    (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  ∀ (F : Functional) (ω : CoadjointOrbit), B ω F F = TetherKernel ω F F
