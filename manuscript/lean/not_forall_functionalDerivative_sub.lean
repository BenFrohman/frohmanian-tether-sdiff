-- FrohmanianTether/TetherNondegeneracy.lean, line 419
public theorem not_forall_functionalDerivative_sub :
    ¬ ∀ ω (F F' : CoadjointOrbit → ℝ), FunctionalDerivative (fun η => F η - F' η) ω =
      FunctionalDerivative F ω - FunctionalDerivative F' ω := ...
