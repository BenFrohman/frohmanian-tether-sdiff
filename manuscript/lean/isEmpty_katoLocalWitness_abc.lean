/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 762

/-!
# manuscript.lean.isEmpty_katoLocalWitness_abc

Machine-checked Lean 4 module.
-/

public theorem isEmpty_katoLocalWitness_abc (ν : ℝ) (m : ℤ) {A B C : ℝ}
    (hABC : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) :
    IsEmpty (KatoLocalWitness (abcProfile (2 * Real.pi * m) A B C) ν) := ...
