/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherNondegeneracy.lean, line 320

/-!
# manuscript.lean.tetherKernel_nondegenerate

Machine-checked Lean 4 module.
-/

public theorem tetherKernel_nondegenerate :
    ∃ (ω φ : CoadjointOrbit) (hφ : IsTestDirection φ), IsRegularVorticity ω ∧
      TetherKernel ω (linFun φ) (linFun φ) ≠ 0 := ...
