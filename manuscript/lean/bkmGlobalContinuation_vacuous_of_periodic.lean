-- FrohmanianTether/ExplicitFlows.lean, line 797
public theorem bkmGlobalContinuation_vacuous_of_periodic {u₀ : VelocityField} {ν : ℝ}
    (hp : FrohmanianTether.ClayStatements.IsZ3Periodic u₀) (hne : u₀ ≠ 0) :
    TetheredLyapunov.BKMGlobalContinuation u₀ ν := ...
