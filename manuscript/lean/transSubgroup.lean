/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- FrohmanianTether/TetherEquivariantC1.lean, line 82

/-!
# manuscript.lean.transSubgroup

Machine-checked Lean 4 module.
-/

@[expose] public def transSubgroup : Subgroup G where
  carrier := {g | ∃ h, g = translate h}
  one_mem' := ⟨0, by
    apply Subtype.ext; apply Equiv.ext; intro x; simp [translate]⟩
  mul_mem' := by
    rintro _ _ ⟨h, rfl⟩ ⟨k, rfl⟩
    refine ⟨k + h, ?_⟩
    apply Subtype.ext; apply Equiv.ext; intro x
    simp [translate, add_assoc]
  inv_mem' := by
    rintro _ ⟨h, rfl⟩
    exact ⟨-h, translate_inv h⟩
