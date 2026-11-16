/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 503

/-!
# manuscript.lean.flow_physical_clauses

Machine-checked Lean 4 module.
-/

public theorem flow_physical_clauses (ν k : ℝ) (α β : Fin 3 → ℝ) (j l : Fin 3 → Fin 3) (T : ℝ) :
    (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : T3, DifferentiableAt ℝ (fun s => flow ν k α β j l s x) t) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) T, Continuous (flow ν k α β j l t)) ∧
    (∃ v₀ : VelocityField, ∀ t ≤ (0 : ℝ),
      flow ν k α β j l t = flow ν k α β j l 0 + t • v₀) := ...
