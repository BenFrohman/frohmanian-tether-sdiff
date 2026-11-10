-- FrohmanianTether/TetherWeightProof.lean, line 218
public theorem good_of_two_correctors {β : T3 → ℝ} {lam : (T3 → EuclideanSpace ℝ (Fin 3)) → ℝ}
    (HV : KillsOrth β lam) (Hlin : CoefAdditive lam) {x y w : T3} (hxy : x ≠ y) (hxw : x ≠ w)
    (hyw : y ≠ w) (hy : CoefPt lam y) (hw : CoefPt lam w) : GoodPt β x := ...
