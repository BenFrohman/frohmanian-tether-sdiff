-- FrohmanianTether/TetherDefinitionAudit.lean, line 61
public theorem localTetherBoundV014_constraint_free_of_unbounded {u : TimeDependentVelocity}
    {t Y : ℝ} (hY : 0 ≤ Y) (h : ¬ BddAbove (Set.range fun x => ‖vorticity (u t) x‖)) :
    vorticity_sup_norm (vorticity (u t)) ≤ Y := ...
