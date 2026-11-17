/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ConcreteSDiff.lean, line 112

/-!
# manuscript.lean.not_transitive_on_casimir_levels

Machine-checked Lean 4 module.
-/

theorem not_transitive_on_casimir_levels :
    ¬ ∀ ω₁ ω₂ : CoadjointOrbit,
      (∀ f : ℝ → ℝ, Casimir f ω₁ = Casimir f ω₂) → ∃ g : G, g • ω₁ = ω₂ := ...
