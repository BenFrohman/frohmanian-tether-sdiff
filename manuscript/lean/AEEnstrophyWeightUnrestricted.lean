/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/Uniqueness.lean, line 517

/-!
# manuscript.lean.AEEnstrophyWeightUnrestricted

Machine-checked Lean 4 module.
-/

@[expose] public def AEEnstrophyWeightUnrestricted
    (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  ∀ α, HasTetherKernelDensity B α → ∃ c : ℝ, ∀ ω, IsRegularVorticity ω →
    ∀ᵐ x ∂(MeasureTheory.volume : Measure T3), α ω x = -c * Enstrophy ω
