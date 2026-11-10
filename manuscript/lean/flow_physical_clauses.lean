-- FrohmanianTether/ExplicitFlows.lean, line 503
public theorem flow_physical_clauses (ν k : ℝ) (α β : Fin 3 → ℝ) (j l : Fin 3 → Fin 3) (T : ℝ) :
    (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : T3, DifferentiableAt ℝ (fun s => flow ν k α β j l s x) t) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) T, Continuous (flow ν k α β j l t)) ∧
    (∃ v₀ : VelocityField, ∀ t ≤ (0 : ℝ),
      flow ν k α β j l t = flow ν k α β j l 0 + t • v₀) := ...
