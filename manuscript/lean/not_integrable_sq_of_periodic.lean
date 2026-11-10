-- FrohmanianTether/ExplicitFlows.lean, line 664
public theorem not_integrable_sq_of_periodic {u : VelocityField} (hc : Continuous u)
    (hp : FrohmanianTether.ClayStatements.IsZ3Periodic u) (hne : u ≠ 0) :
    ¬ Integrable (fun x => ‖u x‖ ^ 2) := ...
