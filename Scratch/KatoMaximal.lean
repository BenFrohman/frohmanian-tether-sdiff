/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import Scratch.MildFlux
import Scratch.KatoPonceCommutator
import Scratch.KatoPonceHypotheses
import Scratch.R3BKMContinuation

/-! # Toward `KatoMaximalSolution` along the realized mild path

On the first existence interval `[0, Tfeff)`, the realized mild field is a
Fefferman-class solution with finite continuous `H³` energy, and the
Kato–Ponce `H³` energy inequality holds, because every named hypothesis of
`katoPonce_h3_energy'` has been discharged along `physicalMild`.

This is not yet `KatoMaximalSolution`: that still needs restart from
`Ĥ^{k+1}` data, mild uniqueness, gluing, and the blow-up alternative, so
that the time set is either `[0, ∞)` or a finite maximal interval on which
the `H³` energy is unbounded. -/

open MeasureTheory Real Filter Topology Set
open scoped ENNReal ContDiff

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
namespace KatoMaximal

open NavierStokes3D KatoPonce KatoPonceHypotheses KatoPonceCommutator
open FeffermanMild MildEnergy MildPressureSmooth MildFlux MildTimeDeriv
open MildMomentum SobolevHilbert NonlinearHm
open RepairedTether R3BKM

variable {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀) (hdec : FeffermanDecay u₀)
  {ν : ℝ} (hν : 0 < ν)

lemma isFeffermanSolutionOn_mono {ν T T' : ℝ} {u₀ : VelocityField}
    {u : TimeDependentVelocity} {p : TimeDependentPressure}
    (h : IsFeffermanSolutionOn ν T' u₀ u p) (hTT : T ≤ T') :
    IsFeffermanSolutionOn ν T u₀ u p := by
  have hsub : Ico (0 : ℝ) T ⊆ Ico (0 : ℝ) T' :=
    Ico_subset_Ico_right hTT
  exact ⟨h.1.mono (prod_mono subset_rfl hsub), h.2.1.mono (prod_mono subset_rfl hsub),
    fun t ht => h.2.2.1 t (hsub ht), h.2.2.2.1, fun t ht => h.2.2.2.2 t (hsub ht)⟩

lemma isFeffermanSolutionOn_physicalMild_le (hdiv : ∀ x, div u₀ x = 0) {T : ℝ}
    (hT : T ≤ Tfeff hf hdec hν) :
    IsFeffermanSolutionOn ν T u₀ (physicalMild hf hdec hν) (presMild hf hdec hν) :=
  isFeffermanSolutionOn_mono (isFeffermanSolutionOn_physicalMild hf hdec hν hdiv) hT

lemma sobolevEnergy_physicalMild_lt_top (t : ℝ) :
    sobolevEnergy 3 (physicalMild hf hdec hν t) < ⊤ := by
  have hk : 2 ≤ 7 := by norm_num
  have hle : 5 ≤ 7 + 1 := by norm_num
  rw [physicalMild_eq_pathExt hf hdec hν hk hle t,
    sobolevEnergy_physicalOfHm (le_refl 5)
      (isRealSlice_pathExt hf hdec hν hk (by norm_num) hle t)]
  exact ENNReal.ofReal_lt_top

lemma continuous_hsSq_physicalMild :
    Continuous (fun t => hsSq 3 (physicalMild hf hdec hν t)) := by
  have hk : 2 ≤ 7 := by norm_num
  have hle : 5 ≤ 7 + 1 := by norm_num
  have hfun : (fun t => hsSq 3 (physicalMild hf hdec hν t)) =
      fun t => ‖incl (by norm_num : 3 ≤ 5)
        (pathExt hf hdec hν hk hle t)‖ ^ 2 := by
    funext t
    exact hsSq_physicalMild hf hdec hν t
  rw [hfun]
  exact (continuous_pow 2).comp
    ((incl (by norm_num : 3 ≤ 5)).continuous.comp
      (continuous_inclExt hle (Tfeff_nonneg hf hdec hν)
        (persistPath hf hdec hν hk))).norm

/-- **Kato–Ponce `H³` energy inequality along the realized mild field.** -/
theorem katoPonce_h3_energy_physicalMild (hdiv : ∀ x, div u₀ x = 0) :
    ∃ Ck : ℝ, 0 ≤ Ck ∧
      ∀ s ∈ Ico (0 : ℝ) (Tfeff hf hdec hν),
        ∃ d : ℝ,
          HasDerivWithinAt (fun t => hsSq 3 (physicalMild hf hdec hν t)) d
            (Ici s) s ∧
          d ≤ Ck * gradSup (physicalMild hf hdec hν s) *
            hsSq 3 (physicalMild hf hdec hν s) := by
  obtain ⟨Ck, hCk, hE⟩ := katoPonce_h3_energy'
  refine ⟨Ck, hCk, ?_⟩
  exact hE ν (Tfeff hf hdec hν) u₀ (physicalMild hf hdec hν) (presMild hf hdec hν)
    hν.le (isFeffermanSolutionOn_physicalMild hf hdec hν hdiv)
    (fun t _ => sobolevEnergy_physicalMild_lt_top hf hdec hν t)
    (h3EnergyRightDerivativeFormula_physicalMild hf hdec hν)
    (fun t ht => h3PartialCommutation
      (isFeffermanSolutionOn_physicalMild hf hdec hν hdiv) ht)
    (fun t _ => h3IBPVanishingFlux_physicalMild hf hdec hν hdiv t)

end KatoMaximal

#print axioms KatoMaximal.isFeffermanSolutionOn_mono
#print axioms KatoMaximal.isFeffermanSolutionOn_physicalMild_le
#print axioms KatoMaximal.sobolevEnergy_physicalMild_lt_top
#print axioms KatoMaximal.continuous_hsSq_physicalMild
#print axioms KatoMaximal.katoPonce_h3_energy_physicalMild
