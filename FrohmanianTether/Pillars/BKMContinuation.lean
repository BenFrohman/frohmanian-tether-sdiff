/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import BKMPillar.PeriodicNSContinuation.IntegrabilityAttack
import FrohmanianTether.Pillars.Uniqueness

/-!
# BKM continuation pillar: `PeriodicBKMContinuation ν` is proved for every `ν > 0`

**Source.** The classical periodic theory proved in `BenFrohman/periodic-ns-classical-continuation`
at commit `502ff17` (over `BenFrohman/fefferman-clay-navier-stokes` at `ebcf109`), vendored in
`vendor/BKMPillar` with one mechanical change: the namespace `NavierStokes3D` is renamed to
`FeffermanNavierStokes3D` (and module prefixes are moved under `BKMPillar`), because both upstream
repositories declare `NavierStokes3D.*` names that clash with this library's. The pillar
theorems used here are:

* `PeriodicNSContinuation.periodicLocalExistence_of_nonneg` (Kato local existence, through
  `tstar_eq_top_or_coe`: the lifespan `T*` is positive);
* `PeriodicNSContinuation.Corrected.periodicMaximalSolution_of_uniqueness` with
  `periodicVelocityUniqueness_of_energy` and `periodicEnergyDifferenceEstimate` (one maximal
  solution, from uniqueness by the energy method);
* `PeriodicNSContinuation.periodicBKMCriterion` (Beale–Kato–Majda: if `T*` is finite, then
  `t ↦ ‖ω(t)‖_∞` is not integrable on `[0, T*]`);
* `PeriodicNSContinuation.continuousOn_vorticity_Ico` (continuity, hence measurability, of
  `t ↦ ‖ω(t)‖_∞` on `[0, T*)`);
* `FeffermanClayNS.periodicGlobalOfTstarTop` (`T* = ⊤` gives a global solution).

**Definitions match.** The operators used by both solution classes (`convective`, `laplacian`,
`div`, `pressureGradient`, `curl`, `vorticity`, `vorticity_sup_norm`) are checked equal to this
library's by `rfl`, and the two `ℤ³`-periodicity predicates are equivalent (`isZ3Periodic_iff`).
The two solution classes differ (Fefferman: `[0, T]`, `derivWithin` on `[0, T]`,
`∂ₜu + (u·∇)u = νΔu − ∇p + f`; sdiff: `[0, T)`, `derivWithin` on `[0, ∞)`,
`∂ₜu + (u·∇)u + ∇p = νΔu`), so the conversions are proved: `isPeriodicSmoothSolutionOn_of_fefferman`
(a Fefferman solution on `[0, T]` is an sdiff solution on `[0, T)`) and
`isPeriodicSmoothSolution_of_fefferman` (global solutions).

**What this gives.** `periodicBKMContinuation_of_classical : 0 < ν → PeriodicBKMContinuation ν`,
so the Main Theorem needs only the OPEN tether closing bound:
`clay_B_exact_of_periodic_tether_closing_bound` and
`clay_B_exact_unique_of_periodic_tether_closing_bound`.

**What this does not give.** `PeriodicTetherClosingBound` (a time-uniform `‖ω‖_∞` bound along
every local periodic solution, for all data) is OPEN, and by the Beale–Kato–Majda criterion it is
as hard as Statement (B). Prodi–Serrin is not used. Nothing here proves Statement (B) or the Clay
Millennium Problem.
-/

open Set Filter Topology NavierStokes3D FrohmanianTether.ClayStatements

namespace FrohmanianTether.Pillars

/-! ### The vendored operators are this library's operators (`rfl`) -/

theorem fef_convective_eq : @FeffermanNavierStokes3D.convective = @NavierStokes3D.convective := rfl
theorem fef_laplacian_eq : @FeffermanNavierStokes3D.laplacian = @NavierStokes3D.laplacian := rfl
theorem fef_div_eq : @FeffermanNavierStokes3D.div = @NavierStokes3D.div := rfl
theorem fef_pressureGradient_eq :
    @FeffermanNavierStokes3D.pressureGradient = @NavierStokes3D.pressureGradient := rfl
theorem fef_curl_eq : @FeffermanNavierStokes3D.curl = @NavierStokes3D.curl := rfl
theorem fef_vorticity_eq : @FeffermanNavierStokes3D.vorticity = @NavierStokes3D.vorticity := rfl
theorem fef_vorticity_sup_norm_eq :
    @FeffermanNavierStokes3D.vorticity_sup_norm = @NavierStokes3D.vorticity_sup_norm := rfl

/-- The lattice embeddings agree (`rfl`). -/
theorem fef_intVecToT3_eq : FeffermanClayNS.intVecToT3 = ClayStatements.latticeVec := rfl

/-- The two `ℤ³`-periodicity predicates are equivalent (argument order differs). -/
theorem isZ3Periodic_iff {α : Type*} (g : T3 → α) :
    FeffermanClayNS.IsZ3Periodic g ↔ ClayStatements.IsZ3Periodic g :=
  ⟨fun h k x => h x k, fun h x k => h k x⟩

/-- sdiff admissible data are Fefferman periodic smooth initial data. -/
theorem isPeriodicSmoothInitialData_of {u₀ : VelocityField} (hd : ∀ x, div u₀ x = 0)
    (hs : ContDiff ℝ (⊤ : ℕ∞) u₀) (hp : ClayStatements.IsZ3Periodic u₀) :
    FeffermanClayNS.IsPeriodicSmoothInitialData u₀ :=
  ⟨hs, hd, (isZ3Periodic_iff u₀).2 hp⟩

/-! ### Conversion between the solution classes (proved) -/

private lemma hasDerivWithinAt_slice_Icc' {T : ℝ} {u : TimeDependentVelocity}
    (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × T3 => u q.1 q.2)
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    (x : T3) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => u s x) (derivWithin (fun s => u s x) (Set.Icc (0 : ℝ) T) t)
      (Set.Icc (0 : ℝ) T) t := by
  have hc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => u s x) (Set.Icc (0 : ℝ) T) :=
    hu.comp ((contDiff_id.prodMk contDiff_const).contDiffOn) (fun _ hs => ⟨hs, trivial⟩)
  exact ((hc.differentiableOn (by simp)) t ht).hasDerivWithinAt

private lemma Icc_mem_nhdsWithin_Ici_of_lt {t T : ℝ} (ht : t < T) :
    Set.Icc (0 : ℝ) T ∈ 𝓝[Set.Ici (0 : ℝ)] t := by
  refine mem_nhdsWithin.2 ⟨Set.Iio T, isOpen_Iio, ht, ?_⟩
  rintro a ⟨ha, ha'⟩
  exact ⟨ha', (show a < T from ha).le⟩

/-- **Proved.** A Fefferman periodic smooth solution on `[0, T]` (zero force) is an sdiff
classical periodic solution on `[0, T)`. -/
theorem isPeriodicSmoothSolutionOn_of_fefferman {ν T : ℝ} {u₀ : VelocityField}
    {u : TimeDependentVelocity} {p : TimeDependentPressure}
    (h : FeffermanClayNS.IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p) :
    ClayStatements.IsPeriodicSmoothSolutionOn ν T u₀ u p := by
  obtain ⟨-, hpu, hpp, hu, hp, hNS, hdiv, h0⟩ := h
  refine ⟨hu.mono (Set.prod_mono Set.Ico_subset_Icc_self subset_rfl),
    hp.mono (Set.prod_mono Set.Ico_subset_Icc_self subset_rfl), fun t ht x => ⟨?_, ?_⟩,
    funext h0, fun t ht => ⟨(isZ3Periodic_iff _).1 (hpu t (Set.Ico_subset_Icc_self ht)),
      (isZ3Periodic_iff _).1 (hpp t (Set.Ico_subset_Icc_self ht))⟩⟩
  · have htc := Set.Ico_subset_Icc_self ht
    have hd := (hasDerivWithinAt_slice_Icc' hu x htc).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsWithin_Ici_of_lt ht.2)
    rw [hd.derivWithin ((uniqueDiffOn_Ici 0) t ht.1)]
    have e := hNS t htc x
    rw [add_zero, fef_convective_eq, fef_laplacian_eq, fef_pressureGradient_eq] at e
    rw [← sub_eq_zero] at e ⊢
    rw [← e]
    abel
  · exact hdiv t (Set.Ico_subset_Icc_self ht) x

/-- **Proved.** A Fefferman global periodic smooth solution (Statement (B) class, zero force) is
an sdiff global periodic smooth solution. -/
theorem isPeriodicSmoothSolution_of_fefferman {ν : ℝ} {u₀ : VelocityField}
    {u : TimeDependentVelocity} {p : TimeDependentPressure}
    (h : FeffermanClayNS.IsPeriodicSmoothSolution ν u₀ (fun _ _ => 0) u p) :
    ClayStatements.IsPeriodicSmoothSolution ν u₀ (fun _ _ => 0) u p := by
  obtain ⟨hpu, hpp, hu, hp, hNS, hdiv, h0⟩ := h
  refine ⟨hu, hp, fun t ht x => ⟨?_, hdiv t ht x⟩, funext h0,
    fun t ht => ⟨(isZ3Periodic_iff _).1 (hpu t ht), (isZ3Periodic_iff _).1 (hpp t ht)⟩⟩
  have e := hNS t ht x
  simp only [add_zero] at e
  rw [fef_convective_eq, fef_laplacian_eq, fef_pressureGradient_eq] at e
  rw [← sub_eq_zero] at e ⊢
  refine Eq.trans ?_ e
  module

/-! ### The BKM continuation hypothesis is a theorem -/

/-- **Proved (pillar; standard axioms).** Classical periodic BKM continuation: for `ν > 0`, if
every local classical periodic solution from `u₀` obeys one bound `‖ω‖_∞ ≤ Y`, there is a global
periodic smooth solution. Proof: take the maximal solution (uniqueness + gluing). If its lifespan
`T*` were finite, `‖ω(t)‖_∞` would be continuous and bounded by `Y` on `[0, T*)` (each restriction
to `[0, T']`, `T' < T*`, is an sdiff local solution), hence integrable on `[0, T*]`, contradicting
the Beale–Kato–Majda criterion. So `T* = ⊤`, and the maximal solution is global. -/
theorem periodicBKMContinuation_of_classical {ν : ℝ} (hν : 0 < ν) : PeriodicBKMContinuation ν := by
  rintro u₀ hd hs hp ⟨Y, hY⟩
  have hu₀ := isPeriodicSmoothInitialData_of hd hs hp
  obtain ⟨u, p, hm⟩ := PeriodicNSContinuation.Corrected.periodicMaximalSolution_of_uniqueness
    (PeriodicNSContinuation.Corrected.periodicVelocityUniqueness_of_energy ν
      (PeriodicNSContinuation.Corrected.periodicEnergyDifferenceEstimate hν.le)) hν u₀ hu₀
  have htop : FeffermanClayNS.periodicTstar ν u₀ = ⊤ := by
    rcases PeriodicNSContinuation.tstar_eq_top_or_coe hν hu₀ with h | ⟨T, hT⟩
    · exact h
    · exfalso
      apply PeriodicNSContinuation.periodicBKMCriterion ν hν u₀ hu₀ u p hm T hT
      refine PeriodicNSContinuation.integrableOn_Icc_of_bdd_Ico (M := Y)
        (PeriodicNSContinuation.continuousOn_vorticity_Ico hν hm hT) ?_
      intro t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (FeffermanNavierStokes3D.vorticity_sup_norm_nonneg _)]
      have hsol := hm ((t + T) / 2) (by linarith [ht.1, ht.2])
        (by rw [hT]; exact EReal.coe_lt_coe_iff.2 (by linarith [ht.2]))
      exact hY _ u p (isPeriodicSmoothSolutionOn_of_fefferman hsol) t ⟨ht.1, by linarith [ht.2]⟩
  obtain ⟨u', p', hsol⟩ := FeffermanClayNS.periodicGlobalOfTstarTop ν hν u₀ hu₀ u p hm htop
  exact ⟨u', p', isPeriodicSmoothSolution_of_fefferman hsol⟩

/-! ### Main Theorem with the BKM pillar discharged: only the OPEN tether bound remains -/

/-- **Main Theorem, BKM discharged (proved; CONDITIONAL on one OPEN hypothesis).** The periodic
tether closing bound for every `ν > 0` gives Statement (B). The bound is OPEN and, by the
Beale–Kato–Majda criterion, as hard as Statement (B) itself. This is not a proof of Statement (B). -/
theorem clay_B_exact_of_periodic_tether_closing_bound
    (hclose : ∀ ν > (0 : ℝ), PeriodicTetherClosingBound ν) : Clay_B_exact :=
  clay_B_exact_of_periodic_tether_bound hclose fun _ hν => periodicBKMContinuation_of_classical hν

/-- **Main Theorem with the uniqueness and BKM pillars (proved; CONDITIONAL on one OPEN
hypothesis).** The periodic tether closing bound gives Statement (B) with a unique global
velocity. This is not a proof of Statement (B). -/
theorem clay_B_exact_unique_of_periodic_tether_closing_bound
    (hclose : ∀ ν > (0 : ℝ), PeriodicTetherClosingBound ν) : Clay_B_exact_unique :=
  clay_B_exact_unique_iff.2 (clay_B_exact_of_periodic_tether_closing_bound hclose)

end FrohmanianTether.Pillars
