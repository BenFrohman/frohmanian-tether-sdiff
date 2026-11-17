/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ClayStatements.lean, line 599

/-!
# manuscript.lean.clay_B_exact_of_periodic_tether_bound

Machine-checked Lean 4 module.
-/

public theorem clay_B_exact_of_periodic_tether_bound
    (hclose : ∀ ν > (0 : ℝ), PeriodicTetherClosingBound ν)
    (hBKM : ∀ ν > (0 : ℝ), PeriodicBKMContinuation ν) : Clay_B_exact := ...
