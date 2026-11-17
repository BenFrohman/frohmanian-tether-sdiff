/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 384

/-!
# manuscript.lean.abcProfile_apply

Machine-checked Lean 4 module.
-/

public theorem abcProfile_apply (k A B C : ℝ) (y : T3) :
    abcProfile k A B C y = WithLp.toLp 2
      ![A * Real.sin (k * y 2) + C * Real.cos (k * y 1),
        B * Real.sin (k * y 0) + A * Real.cos (k * y 2),
        C * Real.sin (k * y 1) + B * Real.cos (k * y 0)] := ...
