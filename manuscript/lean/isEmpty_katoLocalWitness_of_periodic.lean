-- FrohmanianTether/ExplicitFlows.lean, line 735
public theorem isEmpty_katoLocalWitness_of_periodic {u₀ : VelocityField} {ν : ℝ}
    (hp : FrohmanianTether.ClayStatements.IsZ3Periodic u₀) (hne : u₀ ≠ 0) :
    IsEmpty (KatoLocalWitness u₀ ν) := ...
