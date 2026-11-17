/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ArnoldGeometric.lean, line 353

/-!
# manuscript.lean.isFunctionalGradient_unique

Machine-checked Lean 4 module.
-/

public theorem isFunctionalGradient_unique {F : CoadjointOrbit → ℝ} {ω : CoadjointOrbit} {g₁ g₂ : L2Field}
    (h₁ : IsFunctionalGradient F ω g₁) (h₂ : IsFunctionalGradient F ω g₂) : g₁ = g₂ := ...
