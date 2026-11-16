/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherWeightProof.lean, line 218

/-!
# manuscript.lean.good_of_two_correctors

Machine-checked Lean 4 module.
-/

public theorem good_of_two_correctors {β : T3 → ℝ} {lam : (T3 → EuclideanSpace ℝ (Fin 3)) → ℝ}
    (HV : KillsOrth β lam) (Hlin : CoefAdditive lam) {x y w : T3} (hxy : x ≠ y) (hxw : x ≠ w)
    (hyw : y ≠ w) (hy : CoefPt lam y) (hw : CoefPt lam w) : GoodPt β x := ...
