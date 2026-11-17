/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 664

/-!
# manuscript.lean.not_integrable_sq_of_periodic

Machine-checked Lean 4 module.
-/

public theorem not_integrable_sq_of_periodic {u : VelocityField} (hc : Continuous u)
    (hp : FrohmanianTether.ClayStatements.IsZ3Periodic u) (hne : u ≠ 0) :
    ¬ Integrable (fun x => ‖u x‖ ^ 2) := ...
