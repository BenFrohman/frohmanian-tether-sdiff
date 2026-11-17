/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 270

/-!
# manuscript.lean.flow_navier_stokes

Machine-checked Lean 4 module.
-/

public theorem flow_navier_stokes (ν k : ℝ) (α β : Fin 3 → ℝ) (j l : Fin 3 → Fin 3)
    (p₀ : PressureField) (hp₀ : Differentiable ℝ p₀)
    (hdiv : ∀ x, div (trigField k α β j l) x = 0)
    (hbal : ∀ x, convective (trigField k α β j l) (trigField k α β j l) x +
      pressureGradient p₀ x = 0) :
    navier_stokes_eq (flow ν k α β j l) (flowPressure ν k p₀) ν := ...
