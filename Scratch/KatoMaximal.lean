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
set_option maxHeartbeats 800000

noncomputable section
namespace KatoMaximal

open NavierStokes3D KatoPonce KatoPonceHypotheses KatoPonceCommutator
open FeffermanMild FeffermanSobolev MildEnergy MildPressureSmooth MildFlux MildTimeDeriv
open MildMomentum SobolevHilbert NonlinearHm PersistenceHm MildExistence ProductH3
open RepairedTether R3BKM Metric

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
