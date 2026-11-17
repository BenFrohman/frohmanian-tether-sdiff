/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherWeightProof.lean, line 259

/-!
# manuscript.lean.bad_finite

Machine-checked Lean 4 module.
-/

public theorem bad_finite {β : T3 → ℝ} {lam : (T3 → EuclideanSpace ℝ (Fin 3)) → ℝ}
    (HV : KillsOrth β lam) (Hlin : CoefAdditive lam) : {x | ¬ GoodPt β x}.Finite := ...
