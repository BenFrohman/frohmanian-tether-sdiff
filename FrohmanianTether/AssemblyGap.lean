/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import FrohmanianTether.CubicSourceCertificate
public import FrohmanianTether.NS_Equations
public import Mathlib.Tactic.Ring

/-!
# Assembly gap

This file does not discharge `hRiccati`, `conditional_regularity_of_open_hyps`,
or `frohmanian_tether_theorem`.

`hRiccati` is a label for the package `∃ C κ'' y` with
`y' ≤ C y² - κ'' y³` and `M ≤ y`. The (removed) input from the unmodified
equation was the cubic source `⟨ω, (ω·∇)u⟩ ≤ C_CZ M³`, hence
`pairing / M ≤ C_CZ M²` when `M > 0`. The continuation code does not
consume that inequality. It unpacks the package and sends it to
`conditional_regularity`.

`conditional_riccati` expands `CorrectedMaxRate`. `conditional_ceiling`
is the phase line of that hypothesized field. Neither constructs `y`,
neither sets `y(t) = ‖ω(t)‖_∞`, and neither derives
`ω · ((ω · ∇) u) ≤ (C_CZ M - κ M²) M²` from the unmodified vorticity equation.

The former `unmodified_max_pairing_is_classical_source` and `unmodified_max_rate_of_cubic_source`
assumed the false pointwise strain bound (`StrainBoundRefutation.not_forall_strain_le_sup_vorticity`)
and were deleted. `classical_source_not_reduced_strain` (scalar algebra) shows that a cubic source
does not imply `ReducedStrain`.
Statement (B) — deriving `ReducedStrain` from the vorticity equation — stays open.
Dropping the `hRiccati` binder is not a proof of it.
-/

namespace Frohmanian.AssemblyGap

open NavierStokes3D CubicSourceAudit

/-- Name of the open package. Not a proof that the package holds. -/
public def hRiccatiName : String := "hRiccati"

/-- Divide the cubic source by `M > 0`: `pairing / M ≤ C M²`.
This is the checked input. It is not the reduced strain. -/
public theorem classical_max_rate_of_cubic_source
    (pairing M C : ℝ) (hM : 0 < M)
    (h : ClassicalStretchingSource pairing M C) :
    pairing / M ≤ C * M ^ 2 := by
  simp only [ClassicalStretchingSource] at h
  rw [div_le_iff₀ hM]
  have hpow : C * M ^ 2 * M = C * M ^ 3 := by ring
  rw [hpow]
  exact h

/-- The proved cubic source does not imply the reduced pairing.
`pairing = C M³` satisfies `ClassicalStretchingSource` and fails
`ReducedStrain` as soon as `M` and `κ` are positive. -/
public theorem classical_source_not_reduced_strain :
    ∃ pairing M C κ : ℝ,
      0 < M ∧ 0 < κ ∧
        ClassicalStretchingSource pairing M C ∧
        ¬ ReducedStrain pairing M C κ := by
  refine ⟨1, 1, 1, 1, zero_lt_one, zero_lt_one, ?_, ?_⟩
  · simp only [ClassicalStretchingSource]
    exact le_of_eq (show (1 : ℝ) = 1 * 1 ^ 3 by ring)
  · intro h
    simp only [ReducedStrain] at h
    have h0 : (1 * 1 - 1 * 1 ^ 2) * 1 ^ 2 = (0 : ℝ) := by ring
    rw [h0] at h
    exact not_le_of_gt zero_lt_one h

end Frohmanian.AssemblyGap
