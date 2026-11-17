/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- Scratch/KatoPonce.lean, lines 508-509

/-!
# papers.local-kato-theory.lean.DH3

Verbatim excerpt (statement only) of the kernel-checked source file named above.
-/

def H3IBPVanishingFlux (u : VelocityField) (p : PressureField) : Prop :=
  ∀ k ∈ Finset.range 4, ∀ α : Fin k → Fin 3, WordIBP u p k α
