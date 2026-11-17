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

The remaining work for `KatoMaximalSolution` is to restart from the
terminal `Ĥ^{k+1}` slice, invoke mild uniqueness of the included `Ĥ³`
shadows, glue past `Tfeff`, and establish the blow-up alternative, so
that the time set is either `[0, ∞)` or a finite maximal interval on which
the `H³` energy is unbounded. -/

open MeasureTheory Real Filter Topology Set
open scoped ENNReal ContDiff

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section
namespace KatoMaximal

open NavierStokes3D KatoPonce KatoPonceHypotheses KatoPonceCommutator
open FeffermanMild FeffermanSobolev MildEnergy MildPressureSmooth MildFlux MildTimeDeriv
open MildMomentum SobolevHilbert NonlinearHm PersistenceHm MildExistence ProductH3
open MildReal RepairedTether R3BKM Metric

section Energy

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

end Energy

/-! ## Restart from a terminal `Ĥ^{k+1}` slice, uniqueness, and gluing -/

section Restart

/-- Restart a mild `Ĥ^{k+1}` path from its terminal slice. The new existence
time is the `Ĥ³` local time of that slice, and the glued path is mild on
the sum of the two intervals. -/
theorem restart_from_slice {k : ℕ} (hk : 2 ≤ k) {ν t0 : ℝ} (hν : 0 < ν)
    (ht0 : 0 ≤ t0) (u₀ : Hm (k + 1)) {u : XTs k t0}
    (hu : IsMildS hk ht0 ν u₀ u) :
    let w0 := u ⟨t0, ⟨ht0, le_rfl⟩⟩
    let τ := localTime ν (incl (three_le_succ hk) w0)
    let hτ := localTime_nonneg hν (incl (three_le_succ hk) w0)
    0 < τ ∧
      ∃ (v : XTs k τ)
        (hmatch : v ⟨0, ⟨le_rfl, hτ⟩⟩ = w0),
        IsMildS hk hτ ν w0 v ∧
        IsMild hτ ν (incl (three_le_succ hk) w0) (inclMap hk v) ∧
        inclMap hk v ∈
          closedBall (0 : XT τ) (rad (incl (three_le_succ hk) w0)) ∧
        IsMildS hk (add_nonneg ht0 hτ) ν u₀
          (glueXTs hk ht0 hτ u v hmatch) := by
  intro w0 τ hτ
  obtain ⟨v, hvS, hv3, hvB⟩ := persist_on_H3_time hk hν w0
  refine ⟨localTime_pos hν _, v, ?hmatch, hvS, hv3, hvB, ?hglue⟩
  · exact isMildS_zero' hk hτ w0 hvS
  · exact isMildS_glue hk hν ht0 hτ u₀ (isMildS_zero' hk hτ w0 hvS) hu hvS

/-- If two mild paths in possibly different Sobolev spaces have the same
included `Ĥ³` initial datum and both lie in the working ball, their `Ĥ³`
shadows agree, by uniqueness of the mild solution in that ball. -/
theorem unique_inclMap_of_eq_incl {k k' : ℕ} (hk : 2 ≤ k) (hk' : 2 ≤ k')
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    {u₀ : Hm (k + 1)} {v₀ : Hm (k' + 1)}
    (hdata : incl (three_le_succ hk) u₀ = incl (three_le_succ hk') v₀)
    (hTδ : T + 2 * Real.sqrt (T / ν) ≤ delta (incl (three_le_succ hk) u₀))
    {u : XTs k T} {v : XTs k' T}
    (huB : inclMap hk u ∈
      closedBall (0 : XT T) (rad (incl (three_le_succ hk) u₀)))
    (hvB : inclMap hk' v ∈
      closedBall (0 : XT T) (rad (incl (three_le_succ hk') v₀)))
    (huM : IsMild hT ν (incl (three_le_succ hk) u₀) (inclMap hk u))
    (hvM : IsMild hT ν (incl (three_le_succ hk') v₀) (inclMap hk' v)) :
    inclMap hk u = inclMap hk' v :=
  unique_mild_in_ball hν hT (incl (three_le_succ hk) u₀) hTδ huB
    (hdata ▸ hvB) huM (hdata ▸ hvM)

lemma inclMap_glue_eval_le {k : ℕ} (hk : 2 ≤ k) {t0 τ : ℝ}
    (ht0 : 0 ≤ t0) (hτ : 0 ≤ τ) (u : XTs k t0) (v : XTs k τ)
    (hmatch : v ⟨0, ⟨le_rfl, hτ⟩⟩ = u ⟨t0, ⟨ht0, le_rfl⟩⟩)
    (t : Icc (0 : ℝ) (t0 + τ)) (ht : (t : ℝ) ≤ t0) :
    inclMap hk (glueXTs hk ht0 hτ u v hmatch) t =
      inclMap hk u ⟨t.1, ⟨t.2.1, ht⟩⟩ :=
  congrArg (incl (three_le_succ hk)) (glue_eval_le hk ht0 hτ u v hmatch t ht)

lemma inclMap_glue_eval_gt {k : ℕ} (hk : 2 ≤ k) {t0 τ : ℝ}
    (ht0 : 0 ≤ t0) (hτ : 0 ≤ τ) (u : XTs k t0) (v : XTs k τ)
    (hmatch : v ⟨0, ⟨le_rfl, hτ⟩⟩ = u ⟨t0, ⟨ht0, le_rfl⟩⟩)
    (t : Icc (0 : ℝ) (t0 + τ)) (ht : t0 < (t : ℝ)) :
    inclMap hk (glueXTs hk ht0 hτ u v hmatch) t =
      inclMap hk v ⟨t.1 - t0, ⟨sub_nonneg.2 ht.le, by linarith [t.2.2]⟩⟩ :=
  congrArg (incl (three_le_succ hk)) (glue_eval_gt hk ht0 hτ u v hmatch t ht)

/-- Gluing preserves uniqueness of included `Ĥ³` shadows. -/
theorem inclMap_glue_unique {k k' : ℕ} (hk : 2 ≤ k) (hk' : 2 ≤ k')
    {t0 τ : ℝ} (ht0 : 0 ≤ t0) (hτ : 0 ≤ τ)
    {u : XTs k t0} {u' : XTs k' t0} {v : XTs k τ} {v' : XTs k' τ}
    (hmatch : v ⟨0, ⟨le_rfl, hτ⟩⟩ = u ⟨t0, ⟨ht0, le_rfl⟩⟩)
    (hmatch' : v' ⟨0, ⟨le_rfl, hτ⟩⟩ = u' ⟨t0, ⟨ht0, le_rfl⟩⟩)
    (hU : inclMap hk u = inclMap hk' u')
    (hV : inclMap hk v = inclMap hk' v') :
    inclMap hk (glueXTs hk ht0 hτ u v hmatch) =
      inclMap hk' (glueXTs hk' ht0 hτ u' v' hmatch') := by
  refine ContinuousMap.ext fun t => ?_
  rcases le_or_gt (t : ℝ) t0 with ht | ht
  · rw [inclMap_glue_eval_le hk ht0 hτ u v hmatch t ht,
      inclMap_glue_eval_le hk' ht0 hτ u' v' hmatch' t ht]
    exact congrArg (fun w : XT t0 => w ⟨t.1, ⟨t.2.1, ht⟩⟩) hU
  · rw [inclMap_glue_eval_gt hk ht0 hτ u v hmatch t ht,
      inclMap_glue_eval_gt hk' ht0 hτ u' v' hmatch' t ht]
    exact congrArg (fun w : XT τ =>
      w ⟨t.1 - t0, ⟨sub_nonneg.2 ht.le, by linarith [t.2.2]⟩⟩) hV

end Restart

section Extend

variable {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀) (hdec : FeffermanDecay u₀)
  {ν : ℝ} (hν : 0 < ν)

/-- The included `Ĥ³` slices of `persistPath` at the endpoint `Tfeff` agree. -/
lemma incl_persistPath_endpoint {k k' : ℕ} (hk : 2 ≤ k) (hk' : 2 ≤ k') :
    incl (three_le_succ hk)
        (persistPath hf hdec hν hk
          ⟨Tfeff hf hdec hν, ⟨Tfeff_nonneg hf hdec hν, le_rfl⟩⟩) =
      incl (three_le_succ hk')
        (persistPath hf hdec hν hk'
          ⟨Tfeff hf hdec hν, ⟨Tfeff_nonneg hf hdec hν, le_rfl⟩⟩) :=
  congrArg (fun w : XT (Tfeff hf hdec hν) =>
      w ⟨Tfeff hf hdec hν, ⟨Tfeff_nonneg hf hdec hν, le_rfl⟩⟩)
    (inclMap_persistPath_unique hf hdec hν hk hk')

/-- The `Ĥ³` local time of the terminal slice of `persistPath`. This is
independent of the Sobolev index `k`. -/
def restartTime {k : ℕ} (hk : 2 ≤ k) : ℝ :=
  localTime ν (incl (three_le_succ hk)
    (persistPath hf hdec hν hk
      ⟨Tfeff hf hdec hν, ⟨Tfeff_nonneg hf hdec hν, le_rfl⟩⟩))

lemma restartTime_pos {k : ℕ} (hk : 2 ≤ k) : 0 < restartTime hf hdec hν hk :=
  localTime_pos hν _

lemma restartTime_nonneg {k : ℕ} (hk : 2 ≤ k) : 0 ≤ restartTime hf hdec hν hk :=
  localTime_nonneg hν _

lemma restartTime_eq {k k' : ℕ} (hk : 2 ≤ k) (hk' : 2 ≤ k') :
    restartTime hf hdec hν hk = restartTime hf hdec hν hk' := by
  unfold restartTime
  rw [incl_persistPath_endpoint hf hdec hν hk hk']

/-- The realized mild path extends by a positive `Ĥ³` local time past
`Tfeff`, by restarting from the terminal `Ĥ^{k+1}` slice and gluing. -/
theorem extend_persistPath {k : ℕ} (hk : 2 ≤ k) :
    0 < restartTime hf hdec hν hk ∧
      ∃ (v : XTs k (restartTime hf hdec hν hk))
        (hmatch : v ⟨0, ⟨le_rfl, restartTime_nonneg hf hdec hν hk⟩⟩ =
          persistPath hf hdec hν hk
            ⟨Tfeff hf hdec hν, ⟨Tfeff_nonneg hf hdec hν, le_rfl⟩⟩),
        IsMildS hk (restartTime_nonneg hf hdec hν hk) ν
          (persistPath hf hdec hν hk
            ⟨Tfeff hf hdec hν, ⟨Tfeff_nonneg hf hdec hν, le_rfl⟩⟩) v ∧
        IsMild (restartTime_nonneg hf hdec hν hk) ν
          (incl (three_le_succ hk)
            (persistPath hf hdec hν hk
              ⟨Tfeff hf hdec hν, ⟨Tfeff_nonneg hf hdec hν, le_rfl⟩⟩))
          (inclMap hk v) ∧
        inclMap hk v ∈
          closedBall (0 : XT (restartTime hf hdec hν hk))
            (rad (incl (three_le_succ hk)
              (persistPath hf hdec hν hk
                ⟨Tfeff hf hdec hν, ⟨Tfeff_nonneg hf hdec hν, le_rfl⟩⟩))) ∧
        IsMildS hk (add_nonneg (Tfeff_nonneg hf hdec hν)
            (restartTime_nonneg hf hdec hν hk)) ν
          (toHmFeff u₀ hf hdec (k + 1))
          (glueXTs hk (Tfeff_nonneg hf hdec hν)
            (restartTime_nonneg hf hdec hν hk)
            (persistPath hf hdec hν hk) v hmatch) :=
  restart_from_slice hk hν (Tfeff_nonneg hf hdec hν)
    (toHmFeff u₀ hf hdec (k + 1)) (persistPath_mildS hf hdec hν hk)

/-- The included `Ĥ³` shadows of restart pieces on the same interval agree
for any two Sobolev indices. -/
theorem inclMap_restart_unique {k k' : ℕ} (hk : 2 ≤ k) (hk' : 2 ≤ k')
    {v : XTs k (restartTime hf hdec hν hk)}
    {v' : XTs k' (restartTime hf hdec hν hk)}
    (hvB : inclMap hk v ∈
      closedBall (0 : XT (restartTime hf hdec hν hk))
        (rad (incl (three_le_succ hk)
          (persistPath hf hdec hν hk
            ⟨Tfeff hf hdec hν, ⟨Tfeff_nonneg hf hdec hν, le_rfl⟩⟩))))
    (hvB' : inclMap hk' v' ∈
      closedBall (0 : XT (restartTime hf hdec hν hk))
        (rad (incl (three_le_succ hk)
          (persistPath hf hdec hν hk
            ⟨Tfeff hf hdec hν, ⟨Tfeff_nonneg hf hdec hν, le_rfl⟩⟩))))
    (hvM : IsMild (restartTime_nonneg hf hdec hν hk) ν
      (incl (three_le_succ hk)
        (persistPath hf hdec hν hk
          ⟨Tfeff hf hdec hν, ⟨Tfeff_nonneg hf hdec hν, le_rfl⟩⟩))
      (inclMap hk v))
    (hvM' : IsMild (restartTime_nonneg hf hdec hν hk) ν
      (incl (three_le_succ hk)
        (persistPath hf hdec hν hk
          ⟨Tfeff hf hdec hν, ⟨Tfeff_nonneg hf hdec hν, le_rfl⟩⟩))
      (inclMap hk' v')) :
    inclMap hk v = inclMap hk' v' := by
  have hTδ : restartTime hf hdec hν hk +
      2 * Real.sqrt (restartTime hf hdec hν hk / ν) ≤
        delta (incl (three_le_succ hk)
          (persistPath hf hdec hν hk
            ⟨Tfeff hf hdec hν, ⟨Tfeff_nonneg hf hdec hν, le_rfl⟩⟩)) :=
    localTime_visc hν _
  exact unique_mild_in_ball hν (restartTime_nonneg hf hdec hν hk)
    (incl (three_le_succ hk)
      (persistPath hf hdec hν hk
        ⟨Tfeff hf hdec hν, ⟨Tfeff_nonneg hf hdec hν, le_rfl⟩⟩))
    hTδ hvB hvB' hvM hvM'

end Extend

/-! ## Iterated restarts and the mild-level blow-up alternative

Iterating `restart_from_slice` from `persistPath` produces a sequence of
mild paths on times `T_n` with `T_0 = Tfeff` and `T_{n+1} = T_n` plus the
`Ĥ³` local time of the current terminal slice. Either the times
`T_n` are unbounded, or they are bounded and the included `Ĥ³` norms of
the terminal slices are unbounded. This is the blow-up alternative at the
level of the mild `Ĥ^{k+1}` path; the Fefferman-class field, pressure, and
Kato–Ponce inequality on the resulting maximal interval are not obtained
here, so `KatoMaximalSolution` remains open. -/

section Blowup

/-- The local `Ĥ^{k+1}` mild path of a slice, on the `Ĥ³` local time of
that slice. -/
noncomputable def restartPath {k : ℕ} (hk : 2 ≤ k) {ν : ℝ} (hν : 0 < ν)
    (w0 : Hm (k + 1)) : XTs k (localTime ν (incl (three_le_succ hk) w0)) :=
  (persist_on_H3_time hk hν w0).choose

lemma restartPath_mildS {k : ℕ} (hk : 2 ≤ k) {ν : ℝ} (hν : 0 < ν)
    (w0 : Hm (k + 1)) :
    IsMildS hk (localTime_nonneg hν (incl (three_le_succ hk) w0)) ν w0
      (restartPath hk hν w0) :=
  (persist_on_H3_time hk hν w0).choose_spec.1

lemma restartPath_zero {k : ℕ} (hk : 2 ≤ k) {ν : ℝ} (hν : 0 < ν)
    (w0 : Hm (k + 1)) :
    restartPath hk hν w0
        ⟨0, ⟨le_rfl, localTime_nonneg hν (incl (three_le_succ hk) w0)⟩⟩ =
      w0 :=
  isMildS_zero' hk (localTime_nonneg hν (incl (three_le_succ hk) w0)) w0
    (restartPath_mildS hk hν w0)

/-- A mild `Ĥ^{k+1}` path on a finite interval, with no cap at the initial
`Ĥ³` local time. -/
structure MildPath {k : ℕ} (hk : 2 ≤ k) (ν : ℝ) (u₀ : Hm (k + 1)) where
  t : ℝ
  ht : 0 ≤ t
  path : XTs k t
  mild : IsMildS hk ht ν u₀ path

noncomputable def MildPath.endpoint {k : ℕ} {hk : 2 ≤ k} {ν : ℝ}
    {u₀ : Hm (k + 1)} (W : MildPath hk ν u₀) : Hm (k + 1) :=
  W.path ⟨W.t, ⟨W.ht, le_rfl⟩⟩

/-- Restart from the terminal slice and glue, extending the existence time
by the `Ĥ³` local time of that slice. -/
noncomputable def MildPath.next {k : ℕ} {hk : 2 ≤ k} {ν : ℝ} (hν : 0 < ν)
    {u₀ : Hm (k + 1)} (W : MildPath hk ν u₀) : MildPath hk ν u₀ where
  t := W.t + localTime ν (incl (three_le_succ hk) W.endpoint)
  ht := add_nonneg W.ht (localTime_nonneg hν (incl (three_le_succ hk) W.endpoint))
  path := glueXTs hk W.ht
    (localTime_nonneg hν (incl (three_le_succ hk) W.endpoint))
    W.path (restartPath hk hν W.endpoint) (restartPath_zero hk hν W.endpoint)
  mild := isMildS_glue hk hν W.ht
    (localTime_nonneg hν (incl (three_le_succ hk) W.endpoint)) u₀
    (restartPath_zero hk hν W.endpoint) W.mild (restartPath_mildS hk hν W.endpoint)

lemma MildPath.next_t {k : ℕ} {hk : 2 ≤ k} {ν : ℝ} (hν : 0 < ν)
    {u₀ : Hm (k + 1)} (W : MildPath hk ν u₀) :
    (W.next hν).t =
      W.t + localTime ν (incl (three_le_succ hk) W.endpoint) :=
  rfl

lemma MildPath.next_t_ge {k : ℕ} {hk : 2 ≤ k} {ν : ℝ} (hν : 0 < ν)
    {u₀ : Hm (k + 1)} (W : MildPath hk ν u₀) :
    W.t ≤ (W.next hν).t :=
  le_add_of_nonneg_right (localTime_nonneg hν _)

/-- A uniform lower bound on the `Ĥ³` local time of any slice whose
included `Ĥ³` norm is at most `R`. -/
def restartSlot (ν R : ℝ) : ℝ :=
  timeSlot ν (1 / (2 * (18 * Cstar * (2 * R + 1) + 1)))

lemma restartSlot_pos {ν R : ℝ} (hν : 0 < ν) (hR : 0 ≤ R) :
    0 < restartSlot ν R :=
  timeSlot_pos hν (one_div_pos.2 (mul_pos (by norm_num)
    (add_pos_of_nonneg_of_pos
      (mul_nonneg (mul_nonneg (by norm_num) Cstar_nonneg)
        (by linarith)) one_pos)))

lemma restartSlot_le_localTime {ν : ℝ} (hν : 0 < ν) {w : Hm 3} {R : ℝ}
    (hR : 0 ≤ R) (hw : ‖w‖ ≤ R) :
    restartSlot ν R ≤ localTime ν w :=
  localTime_ge_of_norm_le hν hR hw

lemma MildPath.next_t_gap_ge {k : ℕ} {hk : 2 ≤ k} {ν : ℝ} (hν : 0 < ν)
    {u₀ : Hm (k + 1)} (W : MildPath hk ν u₀) {R : ℝ} (hR : 0 ≤ R)
    (hW : ‖incl (three_le_succ hk) W.endpoint‖ ≤ R) :
    restartSlot ν R ≤ (W.next hν).t - W.t := by
  rw [MildPath.next_t, add_sub_cancel_left]
  exact restartSlot_le_localTime hν hR hW

section BlowupFeff

variable {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀) (hdec : FeffermanDecay u₀)
  {ν : ℝ} (hν : 0 < ν)

/-- The realized first-interval path, as a `MildPath`. -/
noncomputable def persistMildPath {k : ℕ} (hk : 2 ≤ k) :
    MildPath hk ν (toHmFeff u₀ hf hdec (k + 1)) where
  t := Tfeff hf hdec hν
  ht := Tfeff_nonneg hf hdec hν
  path := persistPath hf hdec hν hk
  mild := persistPath_mildS hf hdec hν hk

lemma persistMildPath_t {k : ℕ} (hk : 2 ≤ k) :
    (persistMildPath hf hdec hν hk).t = Tfeff hf hdec hν :=
  rfl

/-- Iterated restarts of the realized mild path. `iteratePath 0` is the
path on `[0, Tfeff]`, and each successor glues a fresh local existence
interval from the current terminal slice. -/
noncomputable def iteratePath {k : ℕ} (hk : 2 ≤ k) : ℕ →
    MildPath hk ν (toHmFeff u₀ hf hdec (k + 1))
  | 0 => persistMildPath hf hdec hν hk
  | n + 1 => (iteratePath hk n).next hν

lemma iteratePath_zero {k : ℕ} (hk : 2 ≤ k) :
    iteratePath hf hdec hν hk 0 = persistMildPath hf hdec hν hk :=
  rfl

lemma iteratePath_succ {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    iteratePath hf hdec hν hk (n + 1) = (iteratePath hf hdec hν hk n).next hν :=
  rfl

lemma iteratePath_t_mono {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    (iteratePath hf hdec hν hk n).t ≤ (iteratePath hf hdec hν hk (n + 1)).t :=
  MildPath.next_t_ge hν _

lemma iteratePath_t_ge_Tfeff {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    Tfeff hf hdec hν ≤ (iteratePath hf hdec hν hk n).t := by
  induction n with
  | zero => simp [iteratePath, persistMildPath]
  | succ n ih => exact ih.trans (iteratePath_t_mono hf hdec hν hk n)

lemma iteratePath_t_linear {k : ℕ} (hk : 2 ≤ k) {R : ℝ} (hR : 0 ≤ R)
    (hbd : ∀ n, ‖incl (three_le_succ hk) (iteratePath hf hdec hν hk n).endpoint‖ ≤ R)
    (n : ℕ) :
    Tfeff hf hdec hν + n * restartSlot ν R ≤ (iteratePath hf hdec hν hk n).t := by
  induction n with
  | zero => simp [iteratePath, persistMildPath]
  | succ n ih =>
    have hgap :=
      MildPath.next_t_gap_ge hν (iteratePath hf hdec hν hk n) hR (hbd n)
    calc Tfeff hf hdec hν + (n + 1 : ℕ) * restartSlot ν R
        = Tfeff hf hdec hν + n * restartSlot ν R + restartSlot ν R := by
          push_cast; ring
      _ ≤ (iteratePath hf hdec hν hk n).t + restartSlot ν R :=
        add_le_add ih le_rfl
      _ ≤ (iteratePath hf hdec hν hk n).t +
            ((iteratePath hf hdec hν hk (n + 1)).t -
              (iteratePath hf hdec hν hk n).t) :=
        add_le_add le_rfl hgap
      _ = (iteratePath hf hdec hν hk (n + 1)).t := by ring

/-- **Mild-level blow-up alternative.** Either the iterated existence times
are unbounded, or they are bounded and the included `Ĥ³` norms of the
terminal slices are unbounded. -/
theorem mild_blowup_alternative {k : ℕ} (hk : 2 ≤ k) :
    (∀ M : ℝ, ∃ n : ℕ, M < (iteratePath hf hdec hν hk n).t) ∨
      (BddAbove (Set.range fun n => (iteratePath hf hdec hν hk n).t) ∧
        ∀ B : ℝ, ∃ n : ℕ,
          B < ‖incl (three_le_succ hk)
            (iteratePath hf hdec hν hk n).endpoint‖) := by
  by_cases htimes : BddAbove (Set.range fun n => (iteratePath hf hdec hν hk n).t)
  · refine Or.inr ⟨htimes, fun B => ?_⟩
    by_contra hB
    push Not at hB
    have hR : 0 ≤ B := (norm_nonneg _).trans (hB 0)
    have hlin := iteratePath_t_linear hf hdec hν hk hR hB
    have hδpos : 0 < restartSlot ν B := restartSlot_pos hν hR
    obtain ⟨n, hn⟩ := exists_nat_gt ((sSup (Set.range fun n =>
        (iteratePath hf hdec hν hk n).t) - Tfeff hf hdec hν) / restartSlot ν B)
    set Tstar := sSup (Set.range fun n => (iteratePath hf hdec hν hk n).t)
    have hTstar : (iteratePath hf hdec hν hk n).t ≤ Tstar :=
      le_csSup htimes ⟨n, rfl⟩
    have hTfeff_le : Tfeff hf hdec hν ≤ Tstar :=
      le_csSup htimes ⟨0, rfl⟩
    have hdiv : Tstar - Tfeff hf hdec hν < n * restartSlot ν B :=
      (div_lt_iff₀ hδpos).1 hn
    have hcalc : Tstar < (iteratePath hf hdec hν hk n).t := by
      linarith [hlin n, hdiv, hTfeff_le]
    exact hcalc.not_ge hTstar
  · refine Or.inl fun M => ?_
    have := not_bddAbove_iff.1 htimes M
    rcases this with ⟨t, ⟨n, rfl⟩, ht⟩
    exact ⟨n, ht⟩

end BlowupFeff

end Blowup

/-! ## A single field on the maximal interval

The iterated paths for different Sobolev indices have the same existence
times, and their included `Ĥ³` shadows agree. Restricting a later path to
an earlier interval recovers the earlier path, so a single physical field
and Leray pressure can be defined on the union of the intervals. -/

section Lift

variable {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀) (hdec : FeffermanDecay u₀)
  {ν : ℝ} (hν : 0 < ν)

lemma iteratePath_t_le {k : ℕ} (hk : 2 ≤ k) {n m : ℕ} (h : n ≤ m) :
    (iteratePath hf hdec hν hk n).t ≤ (iteratePath hf hdec hν hk m).t := by
  induction m generalizing n with
  | zero =>
    have hn : n = 0 := Nat.eq_zero_of_le_zero h
    subst hn
    exact le_rfl
  | succ m ih =>
    rcases (Nat.le_succ_iff).1 h with hnm | rfl
    · exact (ih hnm).trans (iteratePath_t_mono hf hdec hν hk m)
    · exact le_rfl

lemma iteratePath_succ_eval_le {k : ℕ} (hk : 2 ≤ k) (n : ℕ) {s : ℝ}
    (hs : s ∈ Icc 0 (iteratePath hf hdec hν hk n).t) :
    (iteratePath hf hdec hν hk (n + 1)).path
        ⟨s, ⟨hs.1, hs.2.trans (iteratePath_t_mono hf hdec hν hk n)⟩⟩ =
      (iteratePath hf hdec hν hk n).path ⟨s, hs⟩ :=
  glue_eval_le hk (iteratePath hf hdec hν hk n).ht
    (localTime_nonneg hν
      (incl (three_le_succ hk) (iteratePath hf hdec hν hk n).endpoint))
    (iteratePath hf hdec hν hk n).path
    (restartPath hk hν (iteratePath hf hdec hν hk n).endpoint)
    (restartPath_zero hk hν (iteratePath hf hdec hν hk n).endpoint)
    ⟨s, ⟨hs.1, hs.2.trans (iteratePath_t_mono hf hdec hν hk n)⟩⟩ hs.2

lemma IccExtend_iteratePath_succ {k : ℕ} (hk : 2 ≤ k) (n : ℕ) {s : ℝ}
    (hs : s ∈ Icc 0 (iteratePath hf hdec hν hk n).t) :
    ContinuousMap.IccExtend (iteratePath hf hdec hν hk (n + 1)).ht
        (iteratePath hf hdec hν hk (n + 1)).path s =
      ContinuousMap.IccExtend (iteratePath hf hdec hν hk n).ht
        (iteratePath hf hdec hν hk n).path s := by
  have hs' : s ∈ Icc 0 (iteratePath hf hdec hν hk (n + 1)).t :=
    ⟨hs.1, hs.2.trans (iteratePath_t_mono hf hdec hν hk n)⟩
  rw [ContinuousMap.coe_IccExtend, ContinuousMap.coe_IccExtend,
    Set.IccExtend_of_mem (hx := hs'), Set.IccExtend_of_mem (hx := hs)]
  exact iteratePath_succ_eval_le hf hdec hν hk n hs

lemma IccExtend_iteratePath_mono {k : ℕ} (hk : 2 ≤ k) {n m : ℕ} (hnm : n ≤ m)
    {s : ℝ} (hs : s ∈ Icc 0 (iteratePath hf hdec hν hk n).t) :
    ContinuousMap.IccExtend (iteratePath hf hdec hν hk m).ht
        (iteratePath hf hdec hν hk m).path s =
      ContinuousMap.IccExtend (iteratePath hf hdec hν hk n).ht
        (iteratePath hf hdec hν hk n).path s := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  clear hnm
  induction d with
  | zero => simp
  | succ d ih =>
    have hs' : s ∈ Icc 0 (iteratePath hf hdec hν hk (n + d)).t :=
      ⟨hs.1, hs.2.trans (iteratePath_t_le hf hdec hν hk (Nat.le_add_right n d))⟩
    rw [show n + (d + 1) = n + d + 1 from add_assoc n d 1,
      IccExtend_iteratePath_succ hf hdec hν hk (n + d) hs']
    exact ih

open Classical LerayPressure

/-- Times at which some iterated mild path is defined. -/
def inMaximal {k : ℕ} (hk : 2 ≤ k) (t : ℝ) : Prop :=
  0 ≤ t ∧ ∃ n : ℕ, t ≤ (iteratePath hf hdec hν hk n).t

/-- The maximal time set. -/
def Smax {k : ℕ} (hk : 2 ≤ k) : Set ℝ := {t | inMaximal hf hdec hν hk t}

/-- Physical velocity on the maximal interval, realized from the `k = 2`
iterated path. Outside the interval it is zero; Fefferman-class statements
only constrain subintervals of `Smax`. -/
noncomputable def physicalMaximal : TimeDependentVelocity :=
  fun t =>
    if h : inMaximal hf hdec hν (by norm_num : 2 ≤ 2) t then
      physicalOfHm
        (ContinuousMap.IccExtend
          (iteratePath hf hdec hν (by norm_num : 2 ≤ 2)
            (Classical.choose h.2)).ht
          (iteratePath hf hdec hν (by norm_num : 2 ≤ 2)
            (Classical.choose h.2)).path t)
    else 0

/-- Leray pressure of the same `Ĥ³` slice. -/
noncomputable def presMaximal : TimeDependentPressure :=
  fun t =>
    if h : inMaximal hf hdec hν (by norm_num : 2 ≤ 2) t then
      lerayPressure (le_refl 3)
        (ContinuousMap.IccExtend
          (iteratePath hf hdec hν (by norm_num : 2 ≤ 2)
            (Classical.choose h.2)).ht
          (iteratePath hf hdec hν (by norm_num : 2 ≤ 2)
            (Classical.choose h.2)).path t)
    else 0

/-- The realized field at a time in the `n`-th interval is the physical field
of that iterated path, independently of the choice of later index. -/
lemma physicalMaximal_eq_iterate {t : ℝ} (ht : 0 ≤ t) (n : ℕ)
    (hn : t ≤ (iteratePath hf hdec hν (by norm_num : 2 ≤ 2) n).t) :
    physicalMaximal hf hdec hν t =
      physicalOfHm
        (ContinuousMap.IccExtend
          (iteratePath hf hdec hν (by norm_num : 2 ≤ 2) n).ht
          (iteratePath hf hdec hν (by norm_num : 2 ≤ 2) n).path t) := by
  have ht2 : inMaximal hf hdec hν (by norm_num : 2 ≤ 2) t := ⟨ht, n, hn⟩
  unfold physicalMaximal
  rw [dif_pos ht2]
  set n2 := Classical.choose ht2.2
  have hn2 : t ≤ (iteratePath hf hdec hν (by norm_num : 2 ≤ 2) n2).t :=
    Classical.choose_spec ht2.2
  set N := max n n2
  have hs : t ∈ Icc 0 (iteratePath hf hdec hν (by norm_num : 2 ≤ 2) n).t :=
    ⟨ht, hn⟩
  have hs2 : t ∈ Icc 0 (iteratePath hf hdec hν (by norm_num : 2 ≤ 2) n2).t :=
    ⟨ht, hn2⟩
  have hleft :=
    IccExtend_iteratePath_mono hf hdec hν (by norm_num : 2 ≤ 2)
      (le_max_right n n2) hs2
  have hright :=
    IccExtend_iteratePath_mono hf hdec hν (by norm_num : 2 ≤ 2)
      (le_max_left n n2) hs
  exact (congrArg physicalOfHm hleft.symm).trans (congrArg physicalOfHm hright)

lemma presMaximal_eq_iterate {t : ℝ} (ht : 0 ≤ t) (n : ℕ)
    (hn : t ≤ (iteratePath hf hdec hν (by norm_num : 2 ≤ 2) n).t) :
    presMaximal hf hdec hν t =
      lerayPressure (le_refl 3)
        (ContinuousMap.IccExtend
          (iteratePath hf hdec hν (by norm_num : 2 ≤ 2) n).ht
          (iteratePath hf hdec hν (by norm_num : 2 ≤ 2) n).path t) := by
  have ht2 : inMaximal hf hdec hν (by norm_num : 2 ≤ 2) t := ⟨ht, n, hn⟩
  unfold presMaximal
  rw [dif_pos ht2]
  set n2 := Classical.choose ht2.2
  have hn2 : t ≤ (iteratePath hf hdec hν (by norm_num : 2 ≤ 2) n2).t :=
    Classical.choose_spec ht2.2
  have hs : t ∈ Icc 0 (iteratePath hf hdec hν (by norm_num : 2 ≤ 2) n).t :=
    ⟨ht, hn⟩
  have hs2 : t ∈ Icc 0 (iteratePath hf hdec hν (by norm_num : 2 ≤ 2) n2).t :=
    ⟨ht, hn2⟩
  have hleft :=
    IccExtend_iteratePath_mono hf hdec hν (by norm_num : 2 ≤ 2)
      (le_max_right n n2) hs2
  have hright :=
    IccExtend_iteratePath_mono hf hdec hν (by norm_num : 2 ≤ 2)
      (le_max_left n n2) hs
  exact (congrArg (lerayPressure (le_refl 3)) hleft.symm).trans
    (congrArg (lerayPressure (le_refl 3)) hright)

lemma restartPath_mild3 {k : ℕ} (hk : 2 ≤ k) (w0 : Hm (k + 1)) :
    IsMild (localTime_nonneg hν (incl (three_le_succ hk) w0)) ν
      (incl (three_le_succ hk) w0) (inclMap hk (restartPath hk hν w0)) :=
  (persist_on_H3_time hk hν w0).choose_spec.2.1

lemma restartPath_memBall {k : ℕ} (hk : 2 ≤ k) (w0 : Hm (k + 1)) :
    inclMap hk (restartPath hk hν w0) ∈
      closedBall (0 : XT (localTime ν (incl (three_le_succ hk) w0)))
        (rad (incl (three_le_succ hk) w0)) :=
  (persist_on_H3_time hk hν w0).choose_spec.2.2

lemma IccExtend_of_nonpos {T : ℝ} (hT : 0 ≤ T) {E : Type*}
    [TopologicalSpace E] (u : C(Icc (0 : ℝ) T, E)) {s : ℝ} (hs : s ≤ 0) :
    ContinuousMap.IccExtend hT u s = ContinuousMap.IccExtend hT u 0 := by
  change u (projIcc 0 T hT s) = u (projIcc 0 T hT 0)
  rw [projIcc_of_le_left (h := hT) hs, projIcc_left (h := hT)]

lemma IccExtend_of_ge {T : ℝ} (hT : 0 ≤ T) {E : Type*}
    [TopologicalSpace E] (u : C(Icc (0 : ℝ) T, E)) {s : ℝ} (hs : T ≤ s) :
    ContinuousMap.IccExtend hT u s = ContinuousMap.IccExtend hT u T := by
  change u (projIcc 0 T hT s) = u (projIcc 0 T hT T)
  rw [projIcc_of_right_le (h := hT) hs, projIcc_right (h := hT)]

lemma IccExtend_endpoint {k : ℕ} {hk : 2 ≤ k} {ν : ℝ} {u₀ : Hm (k + 1)}
    (W : MildPath hk ν u₀) :
    ContinuousMap.IccExtend W.ht W.path W.t = W.endpoint := by
  rw [ContinuousMap.coe_IccExtend,
    Set.IccExtend_of_mem (hx := ⟨W.ht, le_rfl⟩)]
  rfl

lemma IccExtend_eq_cast {T T' : ℝ} (hTT : T = T') (hT : 0 ≤ T) (hT' : 0 ≤ T')
    {E : Type*} [TopologicalSpace E] (u : C(Icc (0 : ℝ) T, E)) (t : ℝ) :
    ContinuousMap.IccExtend hT u t =
      ContinuousMap.IccExtend hT' (hTT ▸ u) t := by
  subst hTT
  rfl

lemma inclMap_eq_cast {k : ℕ} (hk : 2 ≤ k) {T T' : ℝ} (hTT : T = T')
    (u : XTs k T) : inclMap hk (hTT ▸ u) = hTT ▸ inclMap hk u := by
  subst hTT
  rfl

lemma memBall_cast {T T' : ℝ} (hTT : T = T') {R : ℝ} {u : XT T}
    (hu : u ∈ closedBall (0 : XT T) R) :
    (hTT ▸ u) ∈ closedBall (0 : XT T') R := by
  subst hTT
  exact hu

lemma isMild_cast {T T' : ℝ} (hTT : T = T') (hT : 0 ≤ T) (hT' : 0 ≤ T')
    {u₀ : Hm 3} {u : XT T} (hu : IsMild hT ν u₀ u) :
    IsMild hT' ν u₀ (hTT ▸ u) := by
  subst hTT
  exact hu

/-- Uniqueness of included `Ĥ³` shadows on intervals of equal length,
obtained by substituting the time equality before applying
`unique_inclMap_of_eq_incl`. -/
lemma unique_inclMap_of_eq_incl_times {k k' : ℕ} (hk : 2 ≤ k) (hk' : 2 ≤ k')
    (hν : 0 < ν)
    {T T' : ℝ} (hT : 0 ≤ T) (hT' : 0 ≤ T') (hTT : T = T')
    {w : Hm (k + 1)} {w' : Hm (k' + 1)}
    (hdata : incl (three_le_succ hk) w = incl (three_le_succ hk') w')
    (hTδ : T + 2 * Real.sqrt (T / ν) ≤ delta (incl (three_le_succ hk) w))
    {u : XTs k T} {v : XTs k' T'}
    (huB : inclMap hk u ∈
      closedBall (0 : XT T) (rad (incl (three_le_succ hk) w)))
    (hvB : inclMap hk' v ∈
      closedBall (0 : XT T') (rad (incl (three_le_succ hk') w')))
    (huM : IsMild hT ν (incl (three_le_succ hk) w) (inclMap hk u))
    (hvM : IsMild hT' ν (incl (three_le_succ hk') w') (inclMap hk' v)) :
    inclMap hk u = hTT.symm ▸ inclMap hk' v := by
  subst hTT
  exact unique_inclMap_of_eq_incl hk hk' hν hT hdata hTδ huB hvB huM hvM

/-- If two mild paths of equal duration have the same included `Ĥ³`
initial datum and both lie in the working ball, their included shadows
agree at every real time. The time equality is substituted before the
paths are compared, so the proof never rewrites along `▸`. -/
lemma IccExtend_inclMap_of_eq_incl_times {k k' : ℕ} (hk : 2 ≤ k) (hk' : 2 ≤ k')
    (hν : 0 < ν)
    {T T' : ℝ} (hT : 0 ≤ T) (hT' : 0 ≤ T') (hTT : T = T')
    {w : Hm (k + 1)} {w' : Hm (k' + 1)}
    (hdata : incl (three_le_succ hk) w = incl (three_le_succ hk') w')
    (hTδ : T + 2 * Real.sqrt (T / ν) ≤ delta (incl (three_le_succ hk) w))
    {u : XTs k T} {v : XTs k' T'}
    (huB : inclMap hk u ∈
      closedBall (0 : XT T) (rad (incl (three_le_succ hk) w)))
    (hvB : inclMap hk' v ∈
      closedBall (0 : XT T') (rad (incl (three_le_succ hk') w')))
    (huM : IsMild hT ν (incl (three_le_succ hk) w) (inclMap hk u))
    (hvM : IsMild hT' ν (incl (three_le_succ hk') w') (inclMap hk' v))
    (t : ℝ) :
    ContinuousMap.IccExtend hT (inclMap hk u) t =
      ContinuousMap.IccExtend hT' (inclMap hk' v) t := by
  subst hTT
  exact congrArg (fun p => ContinuousMap.IccExtend hT p t)
    (unique_inclMap_of_eq_incl hk hk' hν hT hdata hTδ huB hvB huM hvM)

/-- If two slices have the same included `Ĥ³` datum, the included
`Ĥ³` shadows of their restart paths agree at every time. -/
theorem IccExtend_restartPath_incl {k k' : ℕ} (hk : 2 ≤ k) (hk' : 2 ≤ k')
    {w : Hm (k + 1)} {w' : Hm (k' + 1)}
    (hdata : incl (three_le_succ hk) w = incl (three_le_succ hk') w') (t : ℝ) :
    incl (three_le_succ hk)
        (ContinuousMap.IccExtend
          (localTime_nonneg hν (incl (three_le_succ hk) w))
          (restartPath hk hν w) t) =
      incl (three_le_succ hk')
        (ContinuousMap.IccExtend
          (localTime_nonneg hν (incl (three_le_succ hk') w'))
          (restartPath hk' hν w') t) := by
  set hτ0 := localTime_nonneg hν (incl (three_le_succ hk) w)
  set hτ0' := localTime_nonneg hν (incl (three_le_succ hk') w')
  have hτ :
      localTime ν (incl (three_le_succ hk) w) =
        localTime ν (incl (three_le_succ hk') w') :=
    congrArg (localTime ν) hdata
  have hL :
      incl (three_le_succ hk)
          (ContinuousMap.IccExtend hτ0 (restartPath hk hν w) t) =
        ContinuousMap.IccExtend hτ0 (inclMap hk (restartPath hk hν w)) t :=
    incl_IccExtend hk hτ0 (restartPath hk hν w) t
  have hR :
      incl (three_le_succ hk')
          (ContinuousMap.IccExtend hτ0' (restartPath hk' hν w') t) =
        ContinuousMap.IccExtend hτ0' (inclMap hk' (restartPath hk' hν w')) t :=
    incl_IccExtend hk' hτ0' (restartPath hk' hν w') t
  have hmid :
      ContinuousMap.IccExtend hτ0 (inclMap hk (restartPath hk hν w)) t =
        ContinuousMap.IccExtend hτ0' (inclMap hk' (restartPath hk' hν w')) t :=
    IccExtend_inclMap_of_eq_incl_times hk hk' hν hτ0 hτ0' hτ hdata
      (localTime_visc hν (incl (three_le_succ hk) w))
      (restartPath_memBall hν hk w) (restartPath_memBall hν hk' w')
      (restartPath_mild3 hν hk w) (restartPath_mild3 hν hk' w') t
  exact hL.trans (hmid.trans hR.symm)

lemma IccExtend_next_le {k : ℕ} {hk : 2 ≤ k} {u₀ : Hm (k + 1)}
    (W : MildPath hk ν u₀) {s : ℝ} (hs : s ≤ W.t) :
    ContinuousMap.IccExtend (W.next hν).ht (W.next hν).path s =
      ContinuousMap.IccExtend W.ht W.path s := by
  rcases le_or_gt 0 s with hs0 | hs0
  · exact IccExtend_glue_le hk W.ht
      (localTime_nonneg hν (incl (three_le_succ hk) W.endpoint))
      W.path (restartPath hk hν W.endpoint)
      (restartPath_zero hk hν W.endpoint) ⟨hs0, hs⟩
  · have hL := IccExtend_of_nonpos (W.next hν).ht (W.next hν).path hs0.le
    have hR := IccExtend_of_nonpos W.ht W.path hs0.le
    have h0 : (0 : ℝ) ∈ Icc 0 W.t := ⟨le_rfl, W.ht⟩
    rw [hL, hR]
    exact IccExtend_glue_le hk W.ht
      (localTime_nonneg hν (incl (three_le_succ hk) W.endpoint))
      W.path (restartPath hk hν W.endpoint)
      (restartPath_zero hk hν W.endpoint) h0

lemma IccExtend_next_gt {k : ℕ} {hk : 2 ≤ k} {u₀ : Hm (k + 1)}
    (W : MildPath hk ν u₀) {s : ℝ} (hs0 : W.t ≤ s)
    (hs : s ∈ Icc 0 (W.next hν).t) :
    ContinuousMap.IccExtend (W.next hν).ht (W.next hν).path s =
      ContinuousMap.IccExtend
        (localTime_nonneg hν (incl (three_le_succ hk) W.endpoint))
        (restartPath hk hν W.endpoint) (s - W.t) :=
  IccExtend_glue_gt hk W.ht
    (localTime_nonneg hν (incl (three_le_succ hk) W.endpoint))
    W.path (restartPath hk hν W.endpoint)
    (restartPath_zero hk hν W.endpoint) hs0 hs

/-- Iterated existence times are independent of the Sobolev index, and the
included `Ĥ³` shadows of the iterated paths agree at every time. -/
theorem iteratePath_incl_unique {k k' : ℕ} (hk : 2 ≤ k) (hk' : 2 ≤ k') (n : ℕ) :
    (iteratePath hf hdec hν hk n).t = (iteratePath hf hdec hν hk' n).t ∧
      ∀ t : ℝ,
        incl (three_le_succ hk)
            (ContinuousMap.IccExtend (iteratePath hf hdec hν hk n).ht
              (iteratePath hf hdec hν hk n).path t) =
          incl (three_le_succ hk')
            (ContinuousMap.IccExtend (iteratePath hf hdec hν hk' n).ht
              (iteratePath hf hdec hν hk' n).path t) := by
  induction n with
  | zero =>
    refine ⟨rfl, fun t => ?_⟩
    have hL :=
      incl_IccExtend hk (Tfeff_nonneg hf hdec hν) (persistPath hf hdec hν hk) t
    have hR :=
      incl_IccExtend hk' (Tfeff_nonneg hf hdec hν) (persistPath hf hdec hν hk') t
    have hmid :=
      congrArg (fun p => ContinuousMap.IccExtend (Tfeff_nonneg hf hdec hν) p t)
        (inclMap_persistPath_unique hf hdec hν hk hk')
    exact hL.trans (hmid.trans hR.symm)
  | succ n ih =>
    obtain ⟨hT, hincl⟩ := ih
    set W := iteratePath hf hdec hν hk n
    set W' := iteratePath hf hdec hν hk' n
    have hend :
        incl (three_le_succ hk) W.endpoint =
          incl (three_le_succ hk') W'.endpoint := by
      have h1 : incl (three_le_succ hk) W.endpoint =
          incl (three_le_succ hk) (ContinuousMap.IccExtend W.ht W.path W.t) :=
        congrArg (incl (three_le_succ hk)) (IccExtend_endpoint W).symm
      have h2 := hincl W.t
      have h3 :
          ContinuousMap.IccExtend W'.ht W'.path W.t =
            ContinuousMap.IccExtend W'.ht W'.path W'.t :=
        congrArg (ContinuousMap.IccExtend W'.ht W'.path) hT
      have h4 : incl (three_le_succ hk')
            (ContinuousMap.IccExtend W'.ht W'.path W'.t) =
          incl (three_le_succ hk') W'.endpoint :=
        congrArg _ (IccExtend_endpoint W')
      exact h1.trans (h2.trans ((congrArg (incl (three_le_succ hk')) h3).trans h4))
    have hτ :
        localTime ν (incl (three_le_succ hk) W.endpoint) =
          localTime ν (incl (three_le_succ hk') W'.endpoint) :=
      congrArg (localTime ν) hend
    have htSucc : (W.next hν).t = (W'.next hν).t := by
      change W.t + localTime ν (incl (three_le_succ hk) W.endpoint) =
        W'.t + localTime ν (incl (three_le_succ hk') W'.endpoint)
      rw [hT, hτ]
    refine ⟨htSucc, fun t => ?_⟩
    change
      incl (three_le_succ hk)
          (ContinuousMap.IccExtend (W.next hν).ht (W.next hν).path t) =
        incl (three_le_succ hk')
          (ContinuousMap.IccExtend (W'.next hν).ht (W'.next hν).path t)
    rcases le_or_gt t W.t with ht | ht
    · have hle := IccExtend_next_le hν W ht
      have htW' : t ≤ W'.t := hT ▸ ht
      have hle' := IccExtend_next_le hν W' htW'
      exact (congrArg (incl (three_le_succ hk)) hle).trans
        ((hincl t).trans (congrArg (incl (three_le_succ hk')) hle'.symm))
    · have ht' : W'.t < t := by rwa [← hT]
      have hpos : 0 ≤ t := W.ht.trans ht.le
      rcases le_or_gt t (W.next hν).t with ht1 | ht1
      · have hs : t ∈ Icc 0 (W.next hν).t := ⟨hpos, ht1⟩
        have ht1' : t ≤ (W'.next hν).t := htSucc ▸ ht1
        have hs' : t ∈ Icc 0 (W'.next hν).t := ⟨hpos, ht1'⟩
        have hgt := IccExtend_next_gt hν W ht.le hs
        have hgt' := IccExtend_next_gt hν W' ht'.le hs'
        have hsub : t - W.t = t - W'.t := congrArg (fun s => t - s) hT
        have hrest := IccExtend_restartPath_incl hν hk hk' hend (t - W'.t)
        have hshift :
            incl (three_le_succ hk)
                (ContinuousMap.IccExtend
                  (localTime_nonneg hν (incl (three_le_succ hk) W.endpoint))
                  (restartPath hk hν W.endpoint) (t - W.t)) =
              incl (three_le_succ hk)
                (ContinuousMap.IccExtend
                  (localTime_nonneg hν (incl (three_le_succ hk) W.endpoint))
                  (restartPath hk hν W.endpoint) (t - W'.t)) :=
          congrArg (fun s =>
            incl (three_le_succ hk)
              (ContinuousMap.IccExtend
                (localTime_nonneg hν (incl (three_le_succ hk) W.endpoint))
                (restartPath hk hν W.endpoint) s)) hsub
        exact (congrArg (incl (three_le_succ hk)) hgt).trans
          (hshift.trans (hrest.trans
            (congrArg (incl (three_le_succ hk')) hgt'.symm)))
      · have hL := IccExtend_of_ge (W.next hν).ht (W.next hν).path ht1.le
        have ht1' : (W'.next hν).t ≤ t := htSucc ▸ ht1.le
        have hR := IccExtend_of_ge (W'.next hν).ht (W'.next hν).path ht1'
        have hW : (W.next hν).t ∈ Icc 0 (W.next hν).t :=
          ⟨(W.next hν).ht, le_rfl⟩
        have hW' : (W'.next hν).t ∈ Icc 0 (W'.next hν).t :=
          ⟨(W'.next hν).ht, le_rfl⟩
        have hnext0 : W.t ≤ (W.next hν).t := MildPath.next_t_ge hν W
        have hnext0' : W'.t ≤ (W'.next hν).t := MildPath.next_t_ge hν W'
        have hgt := IccExtend_next_gt hν W hnext0 hW
        have hgt' := IccExtend_next_gt hν W' hnext0' hW'
        have hsub : (W.next hν).t - W.t = (W'.next hν).t - W'.t := by
          rw [MildPath.next_t, MildPath.next_t, add_sub_cancel_left,
            add_sub_cancel_left, hτ]
        have hrest :=
          IccExtend_restartPath_incl hν hk hk' hend ((W'.next hν).t - W'.t)
        have hshift :
            incl (three_le_succ hk)
                (ContinuousMap.IccExtend
                  (localTime_nonneg hν (incl (three_le_succ hk) W.endpoint))
                  (restartPath hk hν W.endpoint) ((W.next hν).t - W.t)) =
              incl (three_le_succ hk)
                (ContinuousMap.IccExtend
                  (localTime_nonneg hν (incl (three_le_succ hk) W.endpoint))
                  (restartPath hk hν W.endpoint) ((W'.next hν).t - W'.t)) :=
          congrArg (fun s =>
            incl (three_le_succ hk)
              (ContinuousMap.IccExtend
                (localTime_nonneg hν (incl (three_le_succ hk) W.endpoint))
                (restartPath hk hν W.endpoint) s)) hsub
        exact (congrArg (incl (three_le_succ hk)) (hL.trans hgt)).trans
          (hshift.trans (hrest.trans
            (congrArg (incl (three_le_succ hk')) (hgt'.symm.trans hR.symm))))

lemma iteratePath_t_unique {k k' : ℕ} (hk : 2 ≤ k) (hk' : 2 ≤ k') (n : ℕ) :
    (iteratePath hf hdec hν hk n).t = (iteratePath hf hdec hν hk' n).t :=
  (iteratePath_incl_unique hf hdec hν hk hk' n).1

lemma IccExtend_iteratePath_incl {k k' : ℕ} (hk : 2 ≤ k) (hk' : 2 ≤ k')
    (n : ℕ) (t : ℝ) :
    incl (three_le_succ hk)
        (ContinuousMap.IccExtend (iteratePath hf hdec hν hk n).ht
          (iteratePath hf hdec hν hk n).path t) =
      incl (three_le_succ hk')
        (ContinuousMap.IccExtend (iteratePath hf hdec hν hk' n).ht
          (iteratePath hf hdec hν hk' n).path t) :=
  (iteratePath_incl_unique hf hdec hν hk hk' n).2 t

lemma iteratePath_t_strict_mono {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    (iteratePath hf hdec hν hk n).t <
      (iteratePath hf hdec hν hk (n + 1)).t := by
  rw [iteratePath_succ, MildPath.next_t]
  exact lt_add_of_pos_right _ (localTime_pos hν _)

lemma Tfeff_pos : 0 < Tfeff hf hdec hν :=
  localTime_pos hν _

/-- The realized physical field agrees with the physical field of any
iterated path, independently of the Sobolev index. -/
lemma physicalMaximal_eq_iterate_high {k : ℕ} (hk : 2 ≤ k) {t : ℝ} (ht : 0 ≤ t)
    (n : ℕ) (hn : t ≤ (iteratePath hf hdec hν hk n).t) :
    physicalMaximal hf hdec hν t =
      physicalOfHm
        (ContinuousMap.IccExtend (iteratePath hf hdec hν hk n).ht
          (iteratePath hf hdec hν hk n).path t) := by
  have hn2 : t ≤ (iteratePath hf hdec hν (by norm_num : 2 ≤ 2) n).t := by
    rwa [← iteratePath_t_unique hf hdec hν hk (by norm_num : 2 ≤ 2) n]
  rw [physicalMaximal_eq_iterate hf hdec hν ht n hn2,
    ← physicalOfHm_incl (three_le_succ (by norm_num : 2 ≤ 2)),
    IccExtend_iteratePath_incl hf hdec hν (by norm_num : 2 ≤ 2) hk n t,
    physicalOfHm_incl (three_le_succ hk)]

lemma presMaximal_eq_iterate_high {k : ℕ} (hk : 2 ≤ k) {t : ℝ} (ht : 0 ≤ t)
    (n : ℕ) (hn : t ≤ (iteratePath hf hdec hν hk n).t) :
    presMaximal hf hdec hν t =
      lerayPressure (three_le_succ hk)
        (ContinuousMap.IccExtend (iteratePath hf hdec hν hk n).ht
          (iteratePath hf hdec hν hk n).path t) := by
  have hn2 : t ≤ (iteratePath hf hdec hν (by norm_num : 2 ≤ 2) n).t := by
    rwa [← iteratePath_t_unique hf hdec hν hk (by norm_num : 2 ≤ 2) n]
  rw [presMaximal_eq_iterate hf hdec hν ht n hn2]
  refine lerayPressure_congr (le_refl 3) (three_le_succ hk) ?_
  have hinc := IccExtend_iteratePath_incl hf hdec hν
    (by norm_num : 2 ≤ 2) hk n t
  set U := ContinuousMap.IccExtend
      (iteratePath hf hdec hν (by norm_num : 2 ≤ 2) n).ht
      (iteratePath hf hdec hν (by norm_num : 2 ≤ 2) n).path t
  set U' := ContinuousMap.IccExtend (iteratePath hf hdec hν hk n).ht
      (iteratePath hf hdec hν hk n).path t
  have hL :=
    (ProductHm.coeFn_incl_vol (three_le_succ (by norm_num : 2 ≤ 2)) U).symm
  have hR := ProductHm.coeFn_incl_vol (three_le_succ hk) U'
  rw [hinc] at hL
  exact hL.trans hR

lemma inMaximal_iff {k k' : ℕ} (hk : 2 ≤ k) (hk' : 2 ≤ k') (t : ℝ) :
    inMaximal hf hdec hν hk t ↔ inMaximal hf hdec hν hk' t := by
  constructor
  · rintro ⟨ht, n, hn⟩
    exact ⟨ht, n, hn.trans_eq (iteratePath_t_unique hf hdec hν hk hk' n)⟩
  · rintro ⟨ht, n, hn⟩
    exact ⟨ht, n, hn.trans_eq (iteratePath_t_unique hf hdec hν hk' hk n)⟩

lemma Smax_unique {k k' : ℕ} (hk : 2 ≤ k) (hk' : 2 ≤ k') :
    Smax hf hdec hν hk = Smax hf hdec hν hk' := by
  ext t
  exact inMaximal_iff hf hdec hν hk hk' t

lemma Smax_eq_Ici_of_unbounded {k : ℕ} (hk : 2 ≤ k)
    (hunb : ∀ M : ℝ, ∃ n : ℕ, M < (iteratePath hf hdec hν hk n).t) :
    Smax hf hdec hν hk = Ici 0 := by
  ext t
  constructor
  · exact fun ht => ht.1
  · intro ht
    obtain ⟨n, hn⟩ := hunb t
    exact ⟨ht, n, hn.le⟩

lemma iteratePath_t_lt_csSup {k : ℕ} (hk : 2 ≤ k)
    (hbd : BddAbove (Set.range fun n => (iteratePath hf hdec hν hk n).t))
    (n : ℕ) :
    (iteratePath hf hdec hν hk n).t <
      sSup (Set.range fun n => (iteratePath hf hdec hν hk n).t) :=
  lt_of_lt_of_le (iteratePath_t_strict_mono hf hdec hν hk n)
    (le_csSup hbd ⟨n + 1, rfl⟩)

lemma Smax_eq_Ico_of_bounded {k : ℕ} (hk : 2 ≤ k)
    (hbd : BddAbove (Set.range fun n => (iteratePath hf hdec hν hk n).t)) :
    0 < sSup (Set.range fun n => (iteratePath hf hdec hν hk n).t) ∧
      Smax hf hdec hν hk =
        Ico 0 (sSup (Set.range fun n => (iteratePath hf hdec hν hk n).t)) := by
  set Tstar := sSup (Set.range fun n => (iteratePath hf hdec hν hk n).t)
  have hpos : 0 < Tstar :=
    lt_of_lt_of_le (Tfeff_pos hf hdec hν) (le_csSup hbd ⟨0, rfl⟩)
  refine ⟨hpos, ?_⟩
  ext t
  constructor
  · rintro ⟨ht, n, hn⟩
    exact ⟨ht, lt_of_le_of_lt hn (iteratePath_t_lt_csSup hf hdec hν hk hbd n)⟩
  · rintro ⟨ht, htT⟩
    refine ⟨ht, ?_⟩
    by_contra h
    push Not at h
    have : Tstar ≤ t :=
      csSup_le ⟨(iteratePath hf hdec hν hk 0).t, ⟨0, rfl⟩⟩
        fun _ ⟨n, hn⟩ => hn ▸ (h n).le
    exact htT.not_ge this

/-- The maximal time set is either `[0, ∞)` or a half-open interval
`[0, T*)` with `T* > 0`. -/
theorem Smax_eq_Ici_or_Ico {k : ℕ} (hk : 2 ≤ k) :
    Smax hf hdec hν hk = Ici 0 ∨
      ∃ Tstar : ℝ, 0 < Tstar ∧ Smax hf hdec hν hk = Ico 0 Tstar := by
  rcases mild_blowup_alternative hf hdec hν hk with hunb | ⟨hbd, _⟩
  · exact Or.inl (Smax_eq_Ici_of_unbounded hf hdec hν hk hunb)
  · obtain ⟨hpos, heq⟩ := Smax_eq_Ico_of_bounded hf hdec hν hk hbd
    exact Or.inr ⟨_, hpos, heq⟩

/-- If the initial slice is `refl`-fixed, every slice of its restart path is. -/
theorem refl_restartPath {k : ℕ} (hk : 2 ≤ k) (w0 : Hm (k + 1))
    (h0 : refl (k + 1) w0 = w0)
    (t : Icc (0 : ℝ) (localTime ν (incl (three_le_succ hk) w0))) :
    refl (k + 1) (restartPath hk hν w0 t) = restartPath hk hν w0 t := by
  have hτ := localTime_nonneg hν (incl (three_le_succ hk) w0)
  set P := inclMap hk (restartPath hk hν w0)
  have hball := restartPath_memBall hν hk w0
  have hball' : reflPath P ∈
      closedBall (0 : XT (localTime ν (incl (three_le_succ hk) w0)))
        (rad (incl (three_le_succ hk) w0)) := by
    rw [mem_closedBall_zero_iff] at hball ⊢
    exact (norm_reflPath_le P).trans hball
  have hdata : refl 3 (incl (three_le_succ hk) w0) = incl (three_le_succ hk) w0 := by
    rw [refl_incl, h0]
  have hM := restartPath_mild3 hν hk w0
  have hM' := isMild_reflPath hτ hν hdata hM
  have heq := unique_mild_in_ball hν hτ (incl (three_le_succ hk) w0)
    (localTime_visc hν _) hball' hball hM' hM
  have h3 : refl 3 (incl (three_le_succ hk) (restartPath hk hν w0 t)) =
      incl (three_le_succ hk) (restartPath hk hν w0 t) :=
    congrArg (fun w : XT (localTime ν (incl (three_le_succ hk) w0)) => w t) heq
  rw [refl_incl] at h3
  exact incl_injective (three_le_succ hk) h3

end Lift

end KatoMaximal

#print axioms KatoMaximal.isFeffermanSolutionOn_mono
#print axioms KatoMaximal.isFeffermanSolutionOn_physicalMild_le
#print axioms KatoMaximal.sobolevEnergy_physicalMild_lt_top
#print axioms KatoMaximal.continuous_hsSq_physicalMild
#print axioms KatoMaximal.katoPonce_h3_energy_physicalMild
#print axioms KatoMaximal.restart_from_slice
#print axioms KatoMaximal.unique_inclMap_of_eq_incl
#print axioms KatoMaximal.inclMap_glue_unique
#print axioms KatoMaximal.incl_persistPath_endpoint
#print axioms KatoMaximal.restartTime_eq
#print axioms KatoMaximal.extend_persistPath
#print axioms KatoMaximal.inclMap_restart_unique
#print axioms KatoMaximal.restartPath_mildS
#print axioms KatoMaximal.MildPath.next_t_gap_ge
#print axioms KatoMaximal.iteratePath_t_linear
#print axioms KatoMaximal.mild_blowup_alternative
#print axioms KatoMaximal.iteratePath_t_le
#print axioms KatoMaximal.IccExtend_iteratePath_mono
#print axioms KatoMaximal.physicalMaximal_eq_iterate
#print axioms KatoMaximal.presMaximal_eq_iterate
#print axioms KatoMaximal.IccExtend_restartPath_incl
#print axioms KatoMaximal.iteratePath_incl_unique
#print axioms KatoMaximal.iteratePath_t_unique
#print axioms KatoMaximal.IccExtend_iteratePath_incl
#print axioms KatoMaximal.physicalMaximal_eq_iterate_high
#print axioms KatoMaximal.presMaximal_eq_iterate_high
#print axioms KatoMaximal.Smax_unique
#print axioms KatoMaximal.Smax_eq_Ici_or_Ico
#print axioms KatoMaximal.refl_restartPath
