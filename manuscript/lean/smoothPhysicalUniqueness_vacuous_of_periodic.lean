/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 790

/-!
# manuscript.lean.smoothPhysicalUniqueness_vacuous_of_periodic

Machine-checked Lean 4 module.
-/

public theorem smoothPhysicalUniqueness_vacuous_of_periodic {u₀ : VelocityField} {ν : ℝ}
    (hp : FrohmanianTether.ClayStatements.IsZ3Periodic u₀) (hne : u₀ ≠ 0) :
    TetheredLyapunov.SmoothPhysicalUniqueness u₀ ν := ...
