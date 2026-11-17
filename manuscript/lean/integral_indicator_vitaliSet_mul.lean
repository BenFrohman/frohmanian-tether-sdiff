/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherWeight.lean, line 178

/-!
# manuscript.lean.integral_indicator_vitaliSet_mul

Machine-checked Lean 4 module.
-/

public theorem integral_indicator_vitaliSet_mul (f : T3 → ℝ) :
    ∫ x, vitaliSet.indicator (fun _ => (1 : ℝ)) x * f x ∂(MeasureTheory.volume : Measure T3) = 0 := ...
