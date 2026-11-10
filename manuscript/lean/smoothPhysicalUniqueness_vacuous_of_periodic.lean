-- FrohmanianTether/ExplicitFlows.lean, line 790
public theorem smoothPhysicalUniqueness_vacuous_of_periodic {u₀ : VelocityField} {ν : ℝ}
    (hp : FrohmanianTether.ClayStatements.IsZ3Periodic u₀) (hne : u₀ ≠ 0) :
    TetheredLyapunov.SmoothPhysicalUniqueness u₀ ν := ...
