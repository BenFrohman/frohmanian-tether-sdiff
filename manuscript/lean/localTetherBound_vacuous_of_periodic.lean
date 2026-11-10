-- FrohmanianTether/ExplicitFlows.lean, line 782
public theorem localTetherBound_vacuous_of_periodic {u₀ : VelocityField} {ν : ℝ}
    (hp : FrohmanianTether.ClayStatements.IsZ3Periodic u₀) (hne : u₀ ≠ 0) :
    TetheredLyapunov.LocalTetherBound u₀ ν := ...
