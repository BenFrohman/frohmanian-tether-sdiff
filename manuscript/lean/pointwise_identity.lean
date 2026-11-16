/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherWeightProof.lean, line 287

/-!
# manuscript.lean.pointwise_identity

Machine-checked Lean 4 module.
-/

public theorem pointwise_identity {g χ : T3 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hχ : ∀ z ∈ tsupport g, χ =ᶠ[nhds z] fun _ => 1) (z : T3) :
    pd (fun y => y 0 * g y) 0 z * pd (fun y => y 0 * χ y) 0 z +
        pd (fun y => y 0 * g y) 1 z * pd (fun y => y 0 * χ y) 1 z -
      (pd g 0 z * pd (fun y => y 0 * y 0 / 2 * χ y) 0 z +
        pd g 1 z * pd (fun y => y 0 * y 0 / 2 * χ y) 1 z) = g z := ...
