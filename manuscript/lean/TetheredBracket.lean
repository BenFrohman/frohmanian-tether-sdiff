/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/SymplecticTether.lean, line 205

/-!
# manuscript.lean.TetheredBracket

Machine-checked Lean 4 module.
-/

public noncomputable def TetheredBracket (F G : Functional) (ω : CoadjointOrbit) : ℝ :=
  -- The Frohmanian Symplectic Tether bracket: the classical Arnold Lie–Poisson bracket
  -- plus the minimal quadratic correction (the tether kernel) that satisfies (C1)–(C3).
  -- Canonicity is proved only inside the restricted kernel class and under the explicit
  -- hypotheses of `uniqueness_of_minimal_tether` (Uniqueness.lean); it is NOT an
  -- unconditional uniqueness statement. The correction is symmetric, so this bracket is
  -- not antisymmetric.
  ClassicalBracket F G ω + TetherKernel ω F G
