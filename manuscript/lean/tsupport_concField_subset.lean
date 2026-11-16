/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TestFieldFamily.lean, line 123

/-!
# manuscript.lean.tsupport_concField_subset

Machine-checked Lean 4 module.
-/

public theorem tsupport_concField_subset (x : T3) {r : ℝ} (hr : 0 < r) :
    tsupport (concField x hr).val ⊆ Metric.ball x r := ...
