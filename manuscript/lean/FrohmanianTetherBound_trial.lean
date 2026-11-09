/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
-- NS_Millennium_Proof/Modules/SymplecticTether.lean
@[expose] public abbrev FrohmanianTetherBound (u₀ : VelocityField) (ν : ℝ) : Prop :=
  ∀ u : ℝ → VelocityField, ∀ p : ℝ → PressureField,
    NS_PDE u p ν → u 0 = u₀ → IsPhysicalNSSolution u →
      ∃ Y : ℝ,
        (∀ τ ≥ (0 : ℝ), vorticity_sup_norm (vorticity (u τ)) ≤ Y) ∧
        Continuous (fun τ : ℝ => vorticity_sup_norm (vorticity (u τ))) ∧
        (∀ τ ≥ (0 : ℝ), BddAbove (Set.range fun x => ‖vorticity (u τ) x‖))
