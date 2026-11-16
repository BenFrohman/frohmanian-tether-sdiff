/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherWeightProof.lean, line 323

/-!
# manuscript.lean.ae_zero_on_good_ball

Machine-checked Lean 4 module.
-/

public theorem ae_zero_on_good_ball {β : T3 → ℝ}
    (hβ : LocallyIntegrable β (MeasureTheory.volume : Measure T3)) {x : T3} {ε : ℝ} (hε : 0 < ε)
    (hgood : ∀ a b : CoadjointOrbit, IsTestDirection a → IsTestDirection b →
      tsupport a.val ⊆ Metric.ball x ε → tsupport b.val ⊆ Metric.ball x ε → Kills β a b) :
    ∀ᵐ z ∂(MeasureTheory.volume : Measure T3), z ∈ Metric.ball x ε → β z = 0 := ...
