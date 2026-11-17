/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- Scratch/KatoMaximalProperties.lean, lines 29-49

/-!
# papers.local-kato-theory.lean.T2-9

Verbatim excerpt (statement only) of the kernel-checked source file named above.
-/

theorem katoMaximalSolution_properties :
    ∀ (u₀ : VelocityField), ContDiff ℝ ∞ u₀ → FeffermanDecay u₀ →
      ∀ (ν : ℝ), 0 < ν → (∀ x, div u₀ x = 0) →
      ∃ (S : ℕ → Set ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure) (Ck : ℝ),
        0 ≤ Ck ∧
        (∀ t ∈ S 2, sobolevEnergy 3 (u t) < ⊤) ∧
        (∀ s ∈ S 2, ∃ d : ℝ, HasDerivWithinAt (fun t => hsSq 3 (u t)) d (Ici s) s ∧
          d ≤ Ck * gradSup (u s) * hsSq 3 (u s)) ∧
        (∀ t ∈ S 2, H3IBPVanishingFlux (u t) (p t)) ∧
        (∀ T : ℝ, Ico (0 : ℝ) T ⊆ S 2 → IsFeffermanSolutionOn ν T u₀ u p) ∧
        (∀ T : ℝ, Ico (0 : ℝ) T ⊆ S 2 → ∀ t ∈ Ico (0 : ℝ) T, ∀ x : T3,
          derivWithin (fun s => u s x) (Ici 0) t + convective (u t) (u t) x +
              pressureGradient (p t) x = ν • laplacian (u t) x + 0) ∧
        (∀ T : ℝ, Ico (0 : ℝ) T ⊆ S 2 → ∀ t ∈ Ico (0 : ℝ) T,
          ∫⁻ x, ‖u t x‖ₑ ^ 2 ≤ ∫⁻ x, ‖u₀ x‖ₑ ^ 2) ∧
        (∀ k : ℕ, 2 ≤ k → ContinuousOn (fun t => hsSq 3 (u t)) (S k)) ∧
        (∀ k : ℕ, 2 ≤ k → S k = Ici (0 : ℝ) ∨
          ∃ Tstar : ℝ, 0 < Tstar ∧ S k = Ico 0 Tstar ∧
            ∀ B : ℝ, ∃ t, t ∈ Ico (0 : ℝ) Tstar ∧ B < hsSq 3 (u t)) ∧
        (∀ k : ℕ, 2 ≤ k → S k = Ici (0 : ℝ) ∨
          ∃ Tstar : ℝ, 0 < Tstar ∧ S k = Ico 0 Tstar)
