/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- Scratch/R3BKMContinuation.lean, lines 88-96

/-!
# papers.local-kato-theory.lean.DKMS

Verbatim excerpt (statement only) of the kernel-checked source file named above.
-/

def KatoMaximalSolution (ν : ℝ) (u₀ : VelocityField) : Prop :=
  ∃ (S : Set ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure) (Ck : ℝ), 0 ≤ Ck ∧
    (∀ T : ℝ, Ico (0 : ℝ) T ⊆ S → IsFeffermanSolutionOn ν T u₀ u p) ∧
    (∀ t ∈ S, sobolevEnergy 3 (u t) < ⊤) ∧
    ContinuousOn (fun t => hsSq 3 (u t)) S ∧
    (∀ s ∈ S, ∃ d : ℝ, HasDerivWithinAt (fun t => hsSq 3 (u t)) d (Ici s) s ∧
      d ≤ Ck * gradSup (u s) * hsSq 3 (u s)) ∧
    (S = Ici 0 ∨ ∃ Tstar : ℝ, 0 < Tstar ∧ S = Ico 0 Tstar ∧
      ∀ B : ℝ, ∃ t ∈ S, B < hsSq 3 (u t))
