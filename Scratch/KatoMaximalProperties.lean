/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import Scratch.KatoMaximal

/-!
# Properties of the Kato maximal solution, stated for one solution

`KatoMaximal.katoMaximalSolution_of_feffermanDecay` (Theorem T1 of the local Kato paper) gives
a maximal Fefferman-class solution. Theorems T2–T9 of that paper describe the solution that the
proof constructs (`Smax`, `physicalMaximal`, `presMaximal`). This file states T2–T9 together, for
one solution `(S, u, p)` with constant `Ck`, without naming the construction: there exist a family
of time sets `S k` (`k ≥ 2`), fields `u`, `p` and `Ck ≥ 0` such that, with `S 2` the maximal time
set, every property of T2–T9 holds, together with finiteness of `‖u(t)‖²_{H³}` on `S 2`
(Definition `def:kato` (ii)). The witness is the construction itself.

This is local Kato theory. It does not assert global regularity.
-/

open MeasureTheory NavierStokes3D FrohmanianTether RepairedTether R3BKM KatoPonce Set
open scoped ContDiff

namespace KatoMaximal

/-- Theorems T2–T9 of the local Kato paper, for one maximal solution. -/
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
          ∃ Tstar : ℝ, 0 < Tstar ∧ S k = Ico 0 Tstar) := by
  intro u₀ hf hdec ν hν hdiv
  obtain ⟨Ck, hCk, hKP⟩ := katoPonce_h3_energy_physicalMaximal hf hdec hν hdiv
  let S : ℕ → Set ℝ := fun k => if hk : 2 ≤ k then Smax hf hdec hν hk else ∅
  have hSk : ∀ (k : ℕ) (hk : 2 ≤ k), S k = Smax hf hdec hν hk := fun k hk => dif_pos hk
  have hS2 : S 2 = Smax hf hdec hν (by norm_num : 2 ≤ 2) := hSk 2 (by norm_num)
  refine ⟨S, physicalMaximal hf hdec hν, presMaximal hf hdec hν, Ck, hCk,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hS2]
    exact fun t ht => sobolevEnergy_physicalMaximal_lt_top hf hdec hν ht
  · rw [hS2]
    exact hKP
  · rw [hS2]
    exact fun t ht => h3IBPVanishingFlux_physicalMaximal hf hdec hν hdiv ht
  · rw [hS2]
    exact fun T hS => isFeffermanSolutionOn_physicalMaximal hf hdec hν hdiv hS
  · rw [hS2]
    exact fun T hS t ht x => momentum_physicalMaximal hf hdec hν hdiv hS ht x
  · rw [hS2]
    exact fun T hS => energyInequality_physicalMaximal hf hdec hν hdiv hS
  · intro k hk
    rw [hSk k hk]
    exact continuousOn_hsSq_physicalMaximal hf hdec hν hk
  · intro k hk
    rw [hSk k hk]
    exact hsSq_blowup_alternative hf hdec hν hk
  · intro k hk
    rw [hSk k hk]
    exact Smax_eq_Ici_or_Ico hf hdec hν hk

end KatoMaximal

#print axioms KatoMaximal.katoMaximalSolution_properties
