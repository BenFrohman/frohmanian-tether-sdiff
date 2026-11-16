/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/ExplicitFlows.lean, line 756

/-!
# manuscript.lean.isEmpty_katoLocalWitness_shear

Machine-checked Lean 4 module.
-/

public theorem isEmpty_katoLocalWitness_shear (ν : ℝ) {m : ℤ} (hm : m ≠ 0) {a : ℝ}
    (ha : a ≠ 0) : IsEmpty (KatoLocalWitness (shearProfile (2 * Real.pi * m) a) ν) := ...
