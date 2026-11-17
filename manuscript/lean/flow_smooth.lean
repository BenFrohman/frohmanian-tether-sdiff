/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 465

/-!
# manuscript.lean.flow_smooth

Machine-checked Lean 4 module.
-/

public theorem flow_smooth (ν k : ℝ) (α β : Fin 3 → ℝ) (j l : Fin 3 → Fin 3) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (flow ν k α β j l t) := ...
