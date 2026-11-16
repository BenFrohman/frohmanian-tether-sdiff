/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetheredLyapunov.lean, line 1572

/-!
# manuscript.lean.localTetherBound_of_localTetherRate

Machine-checked Lean 4 module.
-/

public theorem localTetherBound_of_localTetherRate {u₀ : VelocityField} {ν : ℝ}
    (h : LocalTetherRate u₀ ν) : LocalTetherBound u₀ ν := ...
