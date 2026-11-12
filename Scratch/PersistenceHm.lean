import Scratch.NonlinearHm
import Scratch.MildExistence
import Mathlib.Topology.MetricSpace.Contracting

/-! # Persistence of `Ĥ^{k+1}` regularity on the `Ĥ³` existence time

Local mild existence in `C([0,T]; Ĥ^{k+1})` for `k ≥ 2`, commutation of the
inclusion `Ĥ^{k+1} ↪ Ĥ³` with the heat semigroup, product, derivative, Leray
projector and the nonlinearity, and (later in this file) the Duhamel cocycle,
restart, a priori bound depending only on the `Ĥ³` radius, and persistence of
`∩_m Ĥ^m` up to the `Ĥ³` local time. -/

open MeasureTheory Real Filter Topology Set Metric ContinuousMap
open scoped ENNReal NNReal Convolution

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

noncomputable section
namespace PersistenceHm

open LerayHeat SobolevFourier SobolevHilbert HeatSobolev Duhamel DuhamelUp
open ProductEstimate ProductH3 ProductHm
open Nonlinear (Lij derivSym derivSym_meas bound_deriv)
open NonlinearHm
open MildExistence

variable {k : ℕ}

/-! ## Indexing: high space `Ĥ^{k+1}`, source space `Ĥ^k` (`k ≥ 2`) -/

lemma three_le_succ (hk : 2 ≤ k) : 3 ≤ k + 1 := Nat.succ_le_succ hk

lemma two_le_of_two (hk : 2 ≤ k) : 2 ≤ k := hk

/-- Nonlinearity as a map `Ĥ^{k+1} → Ĥ^k`. -/
def NSNsucc (hk : 2 ≤ k) (u : Hm (k + 1)) : Hm k :=
  (Nat.add_sub_cancel k 1) ▸ NSN (three_le_succ hk) u

lemma norm_NSNsucc_le (hk : 2 ≤ k) (u : Hm (k + 1)) :
    ‖NSNsucc hk u‖ ≤ 18 * Cm (k + 1) * ‖u‖ * ‖incl (three_le_succ hk) u‖ :=
  norm_NSN_le (three_le_succ hk) u

lemma norm_NSNsucc_le_sq (hk : 2 ≤ k) (u : Hm (k + 1)) :
    ‖NSNsucc hk u‖ ≤ 18 * Cm (k + 1) * ‖u‖ ^ 2 := by
  refine (norm_NSNsucc_le hk u).trans ?_
  have hC : 0 ≤ 18 * Cm (k + 1) * ‖u‖ :=
    mul_nonneg (mul_nonneg (by norm_num) (Cm_nonneg _)) (norm_nonneg _)
  have hin := norm_incl_le (three_le_succ hk) u
  have : 18 * Cm (k + 1) * ‖u‖ * ‖incl (three_le_succ hk) u‖ ≤
      18 * Cm (k + 1) * ‖u‖ * ‖u‖ :=
    mul_le_mul_of_nonneg_left hin hC
  refine this.trans (le_of_eq ?_)
  ring

lemma norm_NSNsucc_sub_le (hk : 2 ≤ k) (u v : Hm (k + 1)) :
    ‖NSNsucc hk u - NSNsucc hk v‖ ≤ 18 * Cm (k + 1) * (‖u‖ + ‖v‖) * ‖u - v‖ :=
  norm_NSN_sub_le' (three_le_succ hk) u v

/-! ## Commutation of `incl` with pointwise multipliers and the product -/

lemma incl_heatH (hk : 2 ≤ k) (τ : ℝ) (G : Hm (k + 1)) :
    incl (three_le_succ hk) (heatH (k + 1) τ G) =
      heatH 3 τ (incl (three_le_succ hk) G) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_incl (three_le_succ hk) (heatH (k + 1) τ G),
    (ac_ww (k + 1) 3).ae_le (coeFn_heatH τ G),
    coeFn_heatH τ (incl (three_le_succ hk) G),
    coeFn_incl (three_le_succ hk) G] with ξ h1 h2 h3 h4
  rw [h1, h2, h3, h4]

lemma incl_mulF (hk : 2 ≤ k) (L : V →L[ℂ] V →L[ℂ] V) (F G : Hm (k + 1)) :
    incl (three_le_succ hk) (ProductHm.mulF L (three_le_succ hk) F G) =
      ProductH3.mulF L (incl (three_le_succ hk) F) (incl (three_le_succ hk) G) := by
  refine Lp.ext ?_
  have hconvF := coeFn_incl_vol (three_le_succ hk) F
  have hconvG := coeFn_incl_vol (three_le_succ hk) G
  have hE := (ac_μw 3).ae_le
    ((ProductHm.integrable_of_Hm_ge3 (three_le_succ hk) F).ae_convolution_exists L
      (ProductHm.integrable_of_Hm_ge3 (three_le_succ hk) G))
  filter_upwards [coeFn_incl (three_le_succ hk) (ProductHm.mulF L (three_le_succ hk) F G),
    (ac_ww (k + 1) 3).ae_le (ProductHm.coeFn_mulF L (three_le_succ hk) F G),
    ProductH3.coeFn_mulF L (incl (three_le_succ hk) F) (incl (three_le_succ hk) G),
    hE] with ξ h1 h2 h3 hE
  rw [h1, h2, h3]
  refine integral_congr_ae ?_
  filter_upwards [hconvF,
    (quasiMeasurePreserving_sub_left_of_right_invariant (volume : Measure E3) ξ).ae hconvG]
    with η hF hG
  rw [hF, hG]

lemma le_pred_of_succ (hk : 2 ≤ k) : 2 ≤ (k + 1) - 1 := by
  simpa [Nat.add_sub_cancel] using hk

lemma incl_dH (hk : 2 ≤ k) (j : Fin 3) (G : Hm (k + 1)) :
    incl (le_pred_of_succ hk) (dH (one_le_of_three (three_le_succ hk)) j G) =
      Nonlinear.dH j (incl (three_le_succ hk) G) := by
  refine Lp.ext ?_
  have hs1 : 1 ≤ k + 1 := one_le_of_three (three_le_succ hk)
  have hd : (dH hs1 j G : E3 → V) =ᵐ[μw ((k + 1) - 1)]
      fun ξ => derivSym j ξ ((G : E3 → V) ξ) := by
    simpa [dH] using coeFn_wmul (derivSym j) (derivSym_meas j) 1 zero_le_one
      (bound_deriv_pred hs1 j) G
  have hd3 : (Nonlinear.dH j (incl (three_le_succ hk) G) : E3 → V) =ᵐ[μw 2]
      fun ξ => derivSym j ξ ((incl (three_le_succ hk) G : E3 → V) ξ) := by
    simpa [Nonlinear.dH] using coeFn_wmul (derivSym j) (derivSym_meas j) 1 zero_le_one
      (Nonlinear.bound_deriv j) (incl (three_le_succ hk) G)
  filter_upwards [coeFn_incl (le_pred_of_succ hk) (dH hs1 j G),
    (ac_ww ((k + 1) - 1) 2).ae_le hd, hd3,
    (ac_ww 3 2).ae_le (coeFn_incl (three_le_succ hk) G)] with ξ h1 h2 h3 h4
  rw [h1, h2, h3, h4]

lemma incl_lerayH {m m' : ℕ} (h : m' ≤ m) (G : Hm m) :
    incl h (lerayH m G) = lerayH m' (incl h G) := by
  refine Lp.ext ?_
  have hl : (lerayH m G : E3 → V) =ᵐ[μw m] fun ξ => lerSym ξ ((G : E3 → V) ξ) := by
    simpa [lerayH] using
      coeFn_wmul lerSym lerSym_meas 1 zero_le_one (bound_one (m := m) lerSym_norm) G
  have hl' : (lerayH m' (incl h G) : E3 → V) =ᵐ[μw m']
      fun ξ => lerSym ξ ((incl h G : E3 → V) ξ) := by
    simpa [lerayH] using
      coeFn_wmul lerSym lerSym_meas 1 zero_le_one (bound_one (m := m') lerSym_norm) (incl h G)
  filter_upwards [coeFn_incl h (lerayH m G), (ac_ww m m').ae_le hl, hl',
    coeFn_incl h G] with ξ h1 h2 h3 h4
  rw [h1, h2, h3, h4]

lemma incl_divTensor (hk : 2 ≤ k) (u : Hm (k + 1)) :
    incl (le_pred_of_succ hk) (divTensor (three_le_succ hk) u) =
      Nonlinear.divTensor (incl (three_le_succ hk) u) := by
  unfold divTensor Nonlinear.divTensor
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [incl_dH hk j, incl_mulF hk (Lij i j) u u]

lemma incl_NSN (hk : 2 ≤ k) (u : Hm (k + 1)) :
    incl (le_pred_of_succ hk) (NSN (three_le_succ hk) u) =
      Nonlinear.NSN (incl (three_le_succ hk) u) := by
  unfold NSN Nonlinear.NSN
  rw [incl_lerayH (le_pred_of_succ hk), incl_divTensor hk]

#print axioms PersistenceHm.incl_heatH
#print axioms PersistenceHm.incl_mulF
#print axioms PersistenceHm.incl_dH
#print axioms PersistenceHm.incl_lerayH
#print axioms PersistenceHm.incl_divTensor
#print axioms PersistenceHm.incl_NSN


/-! ## Local mild existence in `C([0,T]; Ĥ^{k+1})` -/

lemma pred_succ_eq (hk : 2 ≤ k) : (k + 1) - 1 + 1 = k + 1 :=
  Nat.sub_add_cancel (Nat.le_add_left 1 k)

lemma norm_cast_Hm {m n : ℕ} (e : m = n) (x : Hm m) : ‖e ▸ x‖ = ‖x‖ := by
  cases e; rfl

lemma continuous_eq_rec {m n : ℕ} (e : m = n) :
    Continuous (fun x : Hm m => e ▸ x) := by
  cases e; exact continuous_id

lemma eq_rec_sub {m n : ℕ} (e : m = n) (x y : Hm m) :
    (e ▸ (x - y)) = (e ▸ x) - (e ▸ y) := by
  cases e; rfl

/-- Smoothing Duhamel with output in `Ĥ^{k+1}`. -/
def duhHigh (hk : 2 ≤ k) (ν : ℝ) (G : ℝ → Hm ((k + 1) - 1)) (t : ℝ) : Hm (k + 1) :=
  (pred_succ_eq hk) ▸ duhν ((k + 1) - 1) ν G t

lemma norm_duhHigh (hk : 2 ≤ k) (ν : ℝ) (G : ℝ → Hm ((k + 1) - 1)) (t : ℝ) :
    ‖duhHigh hk ν G t‖ = ‖duhν ((k + 1) - 1) ν G t‖ :=
  norm_cast_Hm (pred_succ_eq hk) _

lemma duhHigh_sub (hk : 2 ≤ k) {ν : ℝ} (hν : 0 < ν) {G H : ℝ → Hm ((k + 1) - 1)}
    (hG : Continuous G) (hH : Continuous H) {t MG MH : ℝ} (ht : 0 ≤ t)
    (hMG0 : 0 ≤ MG) (hMG : ∀ s ∈ Icc 0 t, ‖G s‖ ≤ MG)
    (hMH0 : 0 ≤ MH) (hMH : ∀ s ∈ Icc 0 t, ‖H s‖ ≤ MH) :
    duhHigh hk ν G t - duhHigh hk ν H t =
      duhHigh hk ν (fun s => G s - H s) t := by
  unfold duhHigh
  cases (pred_succ_eq hk)
  exact duhν_sub (m := (k + 1) - 1) hν hG hH ht hMG0 hMG hMH0 hMH

lemma norm_duhHigh_le (hk : 2 ≤ k) {ν : ℝ} (hν : 0 < ν) {G : ℝ → Hm ((k + 1) - 1)}
    (hG : Continuous G) {t M : ℝ} (ht : 0 ≤ t) (hM0 : 0 ≤ M)
    (hM : ∀ s ∈ Icc 0 t, ‖G s‖ ≤ M) :
    ‖duhHigh hk ν G t‖ ≤ M * (t + 2 * Real.sqrt (t / ν)) := by
  rw [norm_duhHigh]
  exact norm_duhν_le hν hG ht hM0 hM

lemma norm_duhHigh_sub_le (hk : 2 ≤ k) {ν : ℝ} (hν : 0 < ν)
    {G H : ℝ → Hm ((k + 1) - 1)} (hG : Continuous G) (hH : Continuous H)
    {t MG MH M : ℝ} (ht : 0 ≤ t)
    (hMG0 : 0 ≤ MG) (hMG : ∀ s ∈ Icc 0 t, ‖G s‖ ≤ MG)
    (hMH0 : 0 ≤ MH) (hMH : ∀ s ∈ Icc 0 t, ‖H s‖ ≤ MH)
    (hM0 : 0 ≤ M) (hM : ∀ s ∈ Icc 0 t, ‖G s - H s‖ ≤ M) :
    ‖duhHigh hk ν G t - duhHigh hk ν H t‖ ≤ M * (t + 2 * Real.sqrt (t / ν)) := by
  rw [duhHigh_sub hk hν hG hH ht hMG0 hMG hMH0 hMH]
  exact norm_duhHigh_le hk hν (hG.sub hH) ht hM0 hM

lemma continuousOn_duhHigh (hk : 2 ≤ k) {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    {G : ℝ → Hm ((k + 1) - 1)} (hG : Continuous G) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ s ∈ Icc 0 T, ‖G s‖ ≤ M) :
    ContinuousOn (duhHigh hk ν G) (Icc 0 T) :=
  (continuous_eq_rec (pred_succ_eq hk)).comp_continuousOn
    (continuousOn_duhν (m := (k + 1) - 1) hν hT hG hM0 hM)

lemma Cm18_nonneg (k : ℕ) : 0 ≤ 18 * Cm (k + 1) :=
  mul_nonneg (by norm_num) (Cm_nonneg _)

lemma Cm36_nonneg (k : ℕ) : 0 ≤ 36 * Cm (k + 1) :=
  mul_nonneg (by norm_num) (Cm_nonneg _)

lemma norm_NSN_le_sq (hk : 2 ≤ k) (u : Hm (k + 1)) :
    ‖NSN (three_le_succ hk) u‖ ≤ 18 * Cm (k + 1) * ‖u‖ ^ 2 := by
  refine (norm_NSN_le (three_le_succ hk) u).trans ?_
  have hC : 0 ≤ 18 * Cm (k + 1) * ‖u‖ :=
    mul_nonneg (Cm18_nonneg k) (norm_nonneg _)
  have hin := norm_incl_le (three_le_succ hk) u
  have : 18 * Cm (k + 1) * ‖u‖ * ‖incl (three_le_succ hk) u‖ ≤
      18 * Cm (k + 1) * ‖u‖ * ‖u‖ :=
    mul_le_mul_of_nonneg_left hin hC
  refine this.trans (le_of_eq ?_); ring

lemma continuous_comp_NSNhigh (hk : 2 ≤ k) {X : Type*} [TopologicalSpace X]
    {G : X → Hm (k + 1)} (hG : Continuous G) {R : ℝ} (hR : ∀ x, ‖G x‖ ≤ R) :
    Continuous (fun x => NSN (three_le_succ hk) (G x)) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  have hlip : ∀ y, ‖NSN (three_le_succ hk) (G y) - NSN (three_le_succ hk) (G x)‖ ≤
      (18 * Cm (k + 1) * (R + R)) * ‖G y - G x‖ := fun y =>
    (norm_NSN_sub_le' (three_le_succ hk) (G y) (G x)).trans <|
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add (hR y) (hR x)) (Cm18_nonneg k))
        (norm_nonneg _)
  have hc : Continuous fun y => (18 * Cm (k + 1) * (R + R)) * ‖G y - G x‖ :=
    continuous_const.mul (hG.sub continuous_const).norm
  exact squeeze_zero (fun _ => norm_nonneg _) hlip
    (by simpa [sub_self, norm_zero, mul_zero] using hc.tendsto x)

abbrev XTs (k : ℕ) (T : ℝ) := C(Icc (0 : ℝ) T, Hm (k + 1))

def radS (u₀ : Hm (k + 1)) : ℝ := 2 * ‖u₀‖ + 1

lemma radS_pos (u₀ : Hm (k + 1)) : 0 < radS u₀ := by
  unfold radS; linarith [norm_nonneg u₀]

lemma radS_nonneg (u₀ : Hm (k + 1)) : 0 ≤ radS u₀ := (radS_pos u₀).le

lemma le_radS (u₀ : Hm (k + 1)) : ‖u₀‖ ≤ radS u₀ := by
  unfold radS; linarith [norm_nonneg u₀]

lemma u0_eq_radS (u₀ : Hm (k + 1)) : ‖u₀‖ = (radS u₀ - 1) / 2 := by
  unfold radS; ring

def deltaS (u₀ : Hm (k + 1)) : ℝ :=
  1 / (2 * (36 * Cm (k + 1) * radS u₀ + 1))

lemma Cm36_rad_nonneg (u₀ : Hm (k + 1)) : 0 ≤ 36 * Cm (k + 1) * radS u₀ :=
  mul_nonneg (Cm36_nonneg k) (radS_nonneg u₀)

lemma denS_pos (u₀ : Hm (k + 1)) : 0 < 2 * (36 * Cm (k + 1) * radS u₀ + 1) :=
  mul_pos (by norm_num) (add_pos_of_nonneg_of_pos (Cm36_rad_nonneg u₀) one_pos)

lemma deltaS_pos (u₀ : Hm (k + 1)) : 0 < deltaS u₀ := one_div_pos.2 (denS_pos u₀)

def localTimeS (ν : ℝ) (u₀ : Hm (k + 1)) : ℝ := timeSlot ν (deltaS u₀)

lemma localTimeS_pos {ν : ℝ} (hν : 0 < ν) (u₀ : Hm (k + 1)) : 0 < localTimeS ν u₀ :=
  timeSlot_pos hν (deltaS_pos u₀)

lemma localTimeS_nonneg {ν : ℝ} (hν : 0 < ν) (u₀ : Hm (k + 1)) : 0 ≤ localTimeS ν u₀ :=
  (localTimeS_pos hν u₀).le

lemma localTimeS_visc {ν : ℝ} (hν : 0 < ν) (u₀ : Hm (k + 1)) :
    localTimeS ν u₀ + 2 * Real.sqrt (localTimeS ν u₀ / ν) ≤ deltaS u₀ :=
  timeSlot_visc hν (deltaS_pos u₀) (localTimeS_nonneg hν u₀) le_rfl

lemma lip_constS_le_half (u₀ : Hm (k + 1)) :
    36 * Cm (k + 1) * radS u₀ * deltaS u₀ ≤ 1 / 2 := by
  unfold deltaS
  set a := 36 * Cm (k + 1) * radS u₀
  have ha : 0 ≤ a := Cm36_rad_nonneg u₀
  have hden : 0 < 2 * (a + 1) := mul_pos (by norm_num) (add_pos_of_nonneg_of_pos ha one_pos)
  change a * (1 / (2 * (a + 1))) ≤ 1 / 2
  rw [mul_one_div]
  refine (div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 2)).2 ?_
  linarith

lemma inv_arithS (u₀ : Hm (k + 1)) :
    ‖u₀‖ + (18 * Cm (k + 1) * radS u₀ ^ 2) * deltaS u₀ ≤ radS u₀ := by
  set R := radS u₀
  have hR0 : 0 ≤ R := radS_nonneg u₀
  rw [u0_eq_radS u₀]
  unfold deltaS
  have hden : 0 < 2 * (36 * Cm (k + 1) * R + 1) := denS_pos u₀
  rw [mul_one_div]
  have htarget :
      (18 * Cm (k + 1) * R ^ 2) / (2 * (36 * Cm (k + 1) * R + 1)) ≤ (R + 1) / 2 := by
    refine (div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 2)).2 ?_
    have : 18 * Cm (k + 1) * R ^ 2 ≤ (36 * Cm (k + 1) * R + 1) * (R + 1) := by
      calc 18 * Cm (k + 1) * R ^ 2
          ≤ 36 * Cm (k + 1) * R ^ 2 + 36 * Cm (k + 1) * R + R + 1 := by
            have h1 : 0 ≤ 18 * Cm (k + 1) * R ^ 2 :=
              mul_nonneg (Cm18_nonneg k) (sq_nonneg _)
            have h2 : 0 ≤ 36 * Cm (k + 1) * R := Cm36_rad_nonneg u₀
            linarith
        _ = (36 * Cm (k + 1) * R + 1) * (R + 1) := by ring
    linarith
  linarith

lemma norm_extUS_le {T : ℝ} (hT : 0 ≤ T) (u : XTs k T) (s : ℝ) :
    ‖(ContinuousMap.IccExtend hT u) s‖ ≤ ‖u‖ := by
  change ‖u (projIcc 0 T hT s)‖ ≤ ‖u‖
  exact norm_coe_le_norm u _

lemma continuous_NSN_extUS (hk : 2 ≤ k) {T : ℝ} (hT : 0 ≤ T) (u : XTs k T) :
    Continuous (fun s => NSN (three_le_succ hk) ((ContinuousMap.IccExtend hT u) s)) :=
  continuous_comp_NSNhigh hk (ContinuousMap.IccExtend hT u).continuous
    (fun s => norm_extUS_le hT u s)

lemma norm_NSN_extUS_le (hk : 2 ≤ k) {T : ℝ} (hT : 0 ≤ T) (u : XTs k T) (s : ℝ) :
    ‖NSN (three_le_succ hk) ((ContinuousMap.IccExtend hT u) s)‖ ≤
      18 * Cm (k + 1) * ‖u‖ ^ 2 :=
  (norm_NSN_le_sq hk _).trans <|
    mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_extUS_le hT u s) 2) (Cm18_nonneg k)

def mildFnS (hk : 2 ≤ k) (ν : ℝ) (u₀ : Hm (k + 1)) {T : ℝ} (hT : 0 ≤ T)
    (u : XTs k T) (t : ℝ) : Hm (k + 1) :=
  heatH (k + 1) (ν * t) u₀ -
    duhHigh hk ν (fun s => NSN (three_le_succ hk) ((ContinuousMap.IccExtend hT u) s)) t

lemma continuousOn_mildFnS (hk : 2 ≤ k) {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (u₀ : Hm (k + 1)) (u : XTs k T) :
    ContinuousOn (mildFnS hk ν u₀ hT u) (Icc 0 T) :=
  ((continuous_heatH u₀).comp (continuous_const.mul continuous_id)).continuousOn.sub
    (continuousOn_duhHigh hk hν hT (continuous_NSN_extUS hk hT u)
      (mul_nonneg (Cm18_nonneg k) (sq_nonneg _))
      (fun s _ => norm_NSN_extUS_le hk hT u s))

def PhiS (hk : 2 ≤ k) {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (u₀ : Hm (k + 1))
    (u : XTs k T) : XTs k T :=
  ContinuousMap.mk (fun t => mildFnS hk ν u₀ hT u t.1)
    ((continuousOn_mildFnS hk hν hT u₀ u).comp_continuous continuous_subtype_val fun t => t.2)

lemma coe_PhiS (hk : 2 ≤ k) {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (u₀ : Hm (k + 1))
    (u : XTs k T) (t : Icc (0 : ℝ) T) :
    PhiS hk hν hT u₀ u t = mildFnS hk ν u₀ hT u t.1 := rfl

lemma norm_mildFnS_le (hk : 2 ≤ k) {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (u₀ : Hm (k + 1)) (u : XTs k T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖mildFnS hk ν u₀ hT u t‖ ≤
      ‖u₀‖ + (18 * Cm (k + 1) * ‖u‖ ^ 2) * (T + 2 * Real.sqrt (T / ν)) := by
  unfold mildFnS
  refine (norm_sub_le _ _).trans (add_le_add (norm_heatH_le (k + 1) (ν * t) u₀) ?_)
  have hM0 : 0 ≤ 18 * Cm (k + 1) * ‖u‖ ^ 2 := mul_nonneg (Cm18_nonneg k) (sq_nonneg _)
  have hbd : ∀ s ∈ Icc 0 t,
      ‖NSN (three_le_succ hk) ((ContinuousMap.IccExtend hT u) s)‖ ≤
        18 * Cm (k + 1) * ‖u‖ ^ 2 :=
    fun s _ => norm_NSN_extUS_le hk hT u s
  refine (norm_duhHigh_le hk hν (continuous_NSN_extUS hk hT u) ht.1 hM0 hbd).trans ?_
  exact mul_le_mul_of_nonneg_left (visc_time_mono hν ht.2 ht.1) hM0

def IsMildS (hk : 2 ≤ k) {T : ℝ} (hT : 0 ≤ T) (ν : ℝ) (u₀ : Hm (k + 1))
    (u : XTs k T) : Prop :=
  ∀ t : Icc (0 : ℝ) T,
    u t = heatH (k + 1) (ν * (t : ℝ)) u₀ -
      duhHigh hk ν (fun s => NSN (three_le_succ hk)
        ((ContinuousMap.IccExtend hT u) s)) (t : ℝ)

lemma isMildS_iff_fixed (hk : 2 ≤ k) {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (u₀ : Hm (k + 1)) (u : XTs k T) :
    IsMildS hk hT ν u₀ u ↔ PhiS hk hν hT u₀ u = u := by
  constructor
  · intro h
    refine ContinuousMap.ext fun t => ?_
    rw [coe_PhiS, mildFnS]
    exact (h t).symm
  · intro h t
    have ht : u t = PhiS hk hν hT u₀ u t := by rw [h]
    rw [ht, coe_PhiS, mildFnS]

#print axioms PersistenceHm.norm_duhHigh_le
#print axioms PersistenceHm.continuousOn_duhHigh


lemma mapsTo_PhiS (hk : 2 ≤ k) {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (u₀ : Hm (k + 1))
    (hTδ : T + 2 * Real.sqrt (T / ν) ≤ deltaS u₀) :
    MapsTo (PhiS hk hν hT u₀) (closedBall (0 : XTs k T) (radS u₀))
      (closedBall (0 : XTs k T) (radS u₀)) := by
  intro u hu
  have hu' : ‖u‖ ≤ radS u₀ := by
    have := mem_closedBall_iff_norm.mp hu
    rwa [sub_zero] at this
  refine mem_closedBall_iff_norm.mpr ?_
  rw [sub_zero]
  refine (ContinuousMap.norm_le (PhiS hk hν hT u₀ u) (radS_nonneg u₀)).2 fun t => ?_
  have eqt : PhiS hk hν hT u₀ u t = mildFnS hk ν u₀ hT u t.1 := coe_PhiS hk hν hT u₀ u t
  rw [eqt]
  have h1 := norm_mildFnS_le hk hν hT u₀ u t.2
  have hquad : 18 * Cm (k + 1) * ‖u‖ ^ 2 ≤ 18 * Cm (k + 1) * radS u₀ ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hu' 2) (Cm18_nonneg k)
  have hstep :
      ‖mildFnS hk ν u₀ hT u t.1‖ ≤
        ‖u₀‖ + (18 * Cm (k + 1) * radS u₀ ^ 2) * (T + 2 * Real.sqrt (T / ν)) :=
    h1.trans (add_le_add le_rfl (mul_le_mul hquad le_rfl (visc_nonneg hν hT)
      (mul_nonneg (Cm18_nonneg k) (sq_nonneg _))))
  have hstep' :
      ‖mildFnS hk ν u₀ hT u t.1‖ ≤ ‖u₀‖ + (18 * Cm (k + 1) * radS u₀ ^ 2) * deltaS u₀ :=
    hstep.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hTδ (mul_nonneg (Cm18_nonneg k) (sq_nonneg _))))
  exact hstep'.trans (inv_arithS u₀)

lemma extUS_sub {T : ℝ} (hT : 0 ≤ T) (u v : XTs k T) (s : ℝ) :
    ContinuousMap.IccExtend hT (u - v) s =
      ContinuousMap.IccExtend hT u s - ContinuousMap.IccExtend hT v s := rfl

lemma norm_NSN_extUS_sub_le (hk : 2 ≤ k) {T : ℝ} (hT : 0 ≤ T) {R : ℝ} (hR : 0 ≤ R)
    {u v : XTs k T} (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) (s : ℝ) :
    ‖NSN (three_le_succ hk) ((ContinuousMap.IccExtend hT u) s) -
        NSN (three_le_succ hk) ((ContinuousMap.IccExtend hT v) s)‖ ≤
      36 * Cm (k + 1) * R * ‖u - v‖ := by
  have h1 := norm_NSN_sub_le' (three_le_succ hk)
    (ContinuousMap.IccExtend hT u s) (ContinuousMap.IccExtend hT v s)
  have hu' : ‖ContinuousMap.IccExtend hT u s‖ ≤ R := (norm_extUS_le hT u s).trans hu
  have hv' : ‖ContinuousMap.IccExtend hT v s‖ ≤ R := (norm_extUS_le hT v s).trans hv
  have hdiff : ‖ContinuousMap.IccExtend hT u s - ContinuousMap.IccExtend hT v s‖ ≤ ‖u - v‖ := by
    rw [← extUS_sub hT u v s]; exact norm_extUS_le hT (u - v) s
  have hsum : ‖ContinuousMap.IccExtend hT u s‖ + ‖ContinuousMap.IccExtend hT v s‖ ≤ R + R :=
    add_le_add hu' hv'
  have hC : 0 ≤ 18 * Cm (k + 1) := Cm18_nonneg k
  refine h1.trans ?_
  have : 18 * Cm (k + 1) *
      (‖ContinuousMap.IccExtend hT u s‖ + ‖ContinuousMap.IccExtend hT v s‖) *
      ‖ContinuousMap.IccExtend hT u s - ContinuousMap.IccExtend hT v s‖ ≤
      18 * Cm (k + 1) * (R + R) * ‖u - v‖ :=
    mul_le_mul (mul_le_mul_of_nonneg_left hsum hC) hdiff
      (norm_nonneg _) (mul_nonneg hC (add_nonneg hR hR))
  refine this.trans (le_of_eq ?_)
  ring

lemma mildFnS_sub (hk : 2 ≤ k) (ν : ℝ) (u₀ : Hm (k + 1)) {T : ℝ} (hT : 0 ≤ T)
    (u v : XTs k T) (t : ℝ) :
    mildFnS hk ν u₀ hT u t - mildFnS hk ν u₀ hT v t =
      duhHigh hk ν (fun s => NSN (three_le_succ hk) ((ContinuousMap.IccExtend hT v) s)) t -
        duhHigh hk ν (fun s => NSN (three_le_succ hk) ((ContinuousMap.IccExtend hT u) s)) t := by
  simp only [mildFnS, sub_sub_sub_cancel_left]

lemma norm_PhiS_sub_le (hk : 2 ≤ k) {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (u₀ : Hm (k + 1))
    {u v : XTs k T} (hu : ‖u‖ ≤ radS u₀) (hv : ‖v‖ ≤ radS u₀) (t : Icc (0 : ℝ) T) :
    ‖PhiS hk hν hT u₀ u t - PhiS hk hν hT u₀ v t‖ ≤
      (36 * Cm (k + 1) * radS u₀ * (T + 2 * Real.sqrt (T / ν))) * ‖u - v‖ := by
  have eu : PhiS hk hν hT u₀ u t = mildFnS hk ν u₀ hT u t.1 := coe_PhiS hk hν hT u₀ u t
  have ev : PhiS hk hν hT u₀ v t = mildFnS hk ν u₀ hT v t.1 := coe_PhiS hk hν hT u₀ v t
  rw [eu, ev, mildFnS_sub]
  rw [norm_sub_rev]
  have hR := radS_nonneg u₀
  have hMG0 : 0 ≤ 18 * Cm (k + 1) * radS u₀ ^ 2 :=
    mul_nonneg (Cm18_nonneg k) (sq_nonneg _)
  have hMG : ∀ s ∈ Icc 0 T,
      ‖NSN (three_le_succ hk) ((ContinuousMap.IccExtend hT u) s)‖ ≤
        18 * Cm (k + 1) * radS u₀ ^ 2 :=
    fun s _ => (norm_NSN_extUS_le hk hT u s).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hu 2) (Cm18_nonneg k))
  have hMH : ∀ s ∈ Icc 0 T,
      ‖NSN (three_le_succ hk) ((ContinuousMap.IccExtend hT v) s)‖ ≤
        18 * Cm (k + 1) * radS u₀ ^ 2 :=
    fun s _ => (norm_NSN_extUS_le hk hT v s).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hv 2) (Cm18_nonneg k))
  have hM0 : 0 ≤ 36 * Cm (k + 1) * radS u₀ * ‖u - v‖ :=
    mul_nonneg (Cm36_rad_nonneg u₀) (norm_nonneg _)
  have hM : ∀ s ∈ Icc 0 t.1,
      ‖NSN (three_le_succ hk) ((ContinuousMap.IccExtend hT u) s) -
          NSN (three_le_succ hk) ((ContinuousMap.IccExtend hT v) s)‖ ≤
        36 * Cm (k + 1) * radS u₀ * ‖u - v‖ :=
    fun s _ => norm_NSN_extUS_sub_le hk hT hR hu hv s
  have hbd := norm_duhHigh_sub_le hk hν (continuous_NSN_extUS hk hT u)
    (continuous_NSN_extUS hk hT v) (t.2.1) hMG0
    (fun s hs => hMG s ⟨hs.1, hs.2.trans t.2.2⟩) hMG0
    (fun s hs => hMH s ⟨hs.1, hs.2.trans t.2.2⟩) hM0 hM
  refine hbd.trans ?_
  have : t.1 + 2 * Real.sqrt (t.1 / ν) ≤ T + 2 * Real.sqrt (T / ν) :=
    visc_time_mono hν t.2.2 t.2.1
  have hK0 : 0 ≤ 36 * Cm (k + 1) * radS u₀ * ‖u - v‖ := hM0
  calc (36 * Cm (k + 1) * radS u₀ * ‖u - v‖) * (t.1 + 2 * Real.sqrt (t.1 / ν))
      ≤ (36 * Cm (k + 1) * radS u₀ * ‖u - v‖) * (T + 2 * Real.sqrt (T / ν)) :=
        mul_le_mul_of_nonneg_left this hK0
    _ = (36 * Cm (k + 1) * radS u₀ * (T + 2 * Real.sqrt (T / ν))) * ‖u - v‖ := by ring

lemma lipschitz_PhiS (hk : 2 ≤ k) {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (u₀ : Hm (k + 1))
    (hTδ : T + 2 * Real.sqrt (T / ν) ≤ deltaS u₀)
    {u v : XTs k T} (hu : u ∈ closedBall (0 : XTs k T) (radS u₀))
    (hv : v ∈ closedBall (0 : XTs k T) (radS u₀)) :
    dist (PhiS hk hν hT u₀ u) (PhiS hk hν hT u₀ v) ≤ (1 / 2) * dist u v := by
  rw [mem_closedBall_iff_norm, sub_zero] at hu hv
  rw [dist_eq_norm, dist_eq_norm]
  have hpt : ∀ t : Icc (0 : ℝ) T,
      ‖(PhiS hk hν hT u₀ u - PhiS hk hν hT u₀ v) t‖ ≤ (1 / 2) * ‖u - v‖ := fun t => by
    have h1 := norm_PhiS_sub_le hk hν hT u₀ hu hv t
    have h2 : 36 * Cm (k + 1) * radS u₀ * (T + 2 * Real.sqrt (T / ν)) ≤
        36 * Cm (k + 1) * radS u₀ * deltaS u₀ :=
      mul_le_mul_of_nonneg_left hTδ (Cm36_rad_nonneg u₀)
    have h3 : 36 * Cm (k + 1) * radS u₀ * (T + 2 * Real.sqrt (T / ν)) * ‖u - v‖ ≤
        (36 * Cm (k + 1) * radS u₀ * deltaS u₀) * ‖u - v‖ :=
      mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    have h4 : (36 * Cm (k + 1) * radS u₀ * deltaS u₀) * ‖u - v‖ ≤ (1 / 2) * ‖u - v‖ :=
      mul_le_mul_of_nonneg_right (lip_constS_le_half u₀) (norm_nonneg _)
    exact h1.trans (h3.trans h4)
  exact (norm_le (PhiS hk hν hT u₀ u - PhiS hk hν hT u₀ v)
    (mul_nonneg (by norm_num) (norm_nonneg _))).2 hpt

lemma contracting_PhiS (hk : 2 ≤ k) {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (u₀ : Hm (k + 1))
    (hTδ : T + 2 * Real.sqrt (T / ν) ≤ deltaS u₀) :
    ContractingWith (1 / 2 : ℝ≥0)
      ((mapsTo_PhiS hk hν hT u₀ hTδ).restrict (PhiS hk hν hT u₀)
        (closedBall (0 : XTs k T) (radS u₀)) (closedBall (0 : XTs k T) (radS u₀))) := by
  refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  simpa [MapsTo.restrict, Subtype.dist_eq] using
    lipschitz_PhiS hk hν hT u₀ hTδ x.2 y.2

lemma const_mem_ballS {T : ℝ} (hT : 0 ≤ T) (u₀ : Hm (k + 1)) :
    const (Icc (0 : ℝ) T) u₀ ∈ closedBall (0 : XTs k T) (radS u₀) := by
  rw [mem_closedBall_iff_norm, sub_zero]
  refine (norm_le (const (Icc (0 : ℝ) T) u₀) (radS_nonneg u₀)).2 fun _ => ?_
  simpa using le_radS u₀

theorem unique_mildS_in_ball (hk : 2 ≤ k) {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (u₀ : Hm (k + 1))
    (hTδ : T + 2 * Real.sqrt (T / ν) ≤ deltaS u₀)
    {u v : XTs k T} (hu : u ∈ closedBall (0 : XTs k T) (radS u₀))
    (hv : v ∈ closedBall (0 : XTs k T) (radS u₀))
    (huM : IsMildS hk hT ν u₀ u) (hvM : IsMildS hk hT ν u₀ v) : u = v := by
  have fu : PhiS hk hν hT u₀ u = u := (isMildS_iff_fixed hk hν hT u₀ u).1 huM
  have fv : PhiS hk hν hT u₀ v = v := (isMildS_iff_fixed hk hν hT u₀ v).1 hvM
  have hd := lipschitz_PhiS hk hν hT u₀ hTδ hu hv
  rw [fu, fv] at hd
  have hnn : 0 ≤ dist u v := dist_nonneg
  have : dist u v = 0 := le_antisymm (by nlinarith) hnn
  exact eq_of_dist_eq_zero this

/-- Local mild existence in `C([0,T]; Ĥ^{k+1})` on the time `localTimeS ν u₀`
depending on `ν` and `‖u₀‖_{Ĥ^{k+1}}`. -/
theorem local_mild_existence_S (hk : 2 ≤ k) (ν : ℝ) (hν : 0 < ν) (u₀ : Hm (k + 1)) :
    let T := localTimeS ν u₀
    0 < T ∧
      ∃ u : XTs k T, u ∈ closedBall (0 : XTs k T) (radS u₀) ∧
        IsMildS hk (localTimeS_nonneg hν u₀) ν u₀ u ∧
        ∀ v ∈ closedBall (0 : XTs k T) (radS u₀),
          IsMildS hk (localTimeS_nonneg hν u₀) ν u₀ v → v = u := by
  set T := localTimeS ν u₀
  have hT : 0 ≤ T := localTimeS_nonneg hν u₀
  have hTδ : T + 2 * Real.sqrt (T / ν) ≤ deltaS u₀ := localTimeS_visc hν u₀
  have hsc : IsComplete (closedBall (0 : XTs k T) (radS u₀)) := isClosed_closedBall.isComplete
  have hsf := mapsTo_PhiS hk hν hT u₀ hTδ
  have hf := contracting_PhiS hk hν hT u₀ hTδ
  have hx : const (Icc (0 : ℝ) T) u₀ ∈ closedBall (0 : XTs k T) (radS u₀) :=
    const_mem_ballS hT u₀
  have he : edist (const (Icc (0 : ℝ) T) u₀)
      (PhiS hk hν hT u₀ (const (Icc (0 : ℝ) T) u₀)) ≠ ⊤ := (edist_lt_top _ _).ne
  obtain ⟨u, hu, hfix, _, _⟩ := hf.exists_fixedPoint' hsc hsf hx he
  refine ⟨localTimeS_pos hν u₀, u, hu, (isMildS_iff_fixed hk hν hT u₀ u).2 (by exact hfix), ?_⟩
  intro v hv hvM
  exact unique_mildS_in_ball hk hν hT u₀ hTδ hv hu hvM
    ((isMildS_iff_fixed hk hν hT u₀ u).2 (by exact hfix))

#print axioms PersistenceHm.local_mild_existence_S
#print axioms PersistenceHm.unique_mildS_in_ball


/-! ## Commutation of `incl` with Duhamel, and the Duhamel cocycle -/

lemma exists_bound_Icc {E : Type*} [SeminormedAddCommGroup E] {f : ℝ → E}
    (hf : Continuous f) (a b : ℝ) : ∃ M ≥ (0 : ℝ), ∀ s ∈ Icc a b, ‖f s‖ ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨max M 0, le_max_right _ _, fun s hs => (hM s hs).trans (le_max_left _ _)⟩

lemma incl_heatUp {m m' : ℕ} (h : m' ≤ m) {τ : ℝ} (hτ : 0 < τ) (G : Hm m) :
    incl (Nat.succ_le_succ h) (heatUp m hτ G) = heatUp m' hτ (incl h G) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_incl (Nat.succ_le_succ h) (heatUp m hτ G),
    (ac_ww (m + 1) (m' + 1)).ae_le (coeFn_heatUp hτ G),
    coeFn_heatUp hτ (incl h G),
    (ac_ww m' (m' + 1)).ae_le (coeFn_incl h G)] with ξ h1 h2 h3 h4
  rw [h1, h2, h3, h4]

lemma incl_upI {m m' : ℕ} (h : m' ≤ m) (G : ℝ → Hm m) (t s : ℝ) :
    incl (Nat.succ_le_succ h) (upI G t s) = upI (fun σ => incl h (G σ)) t s := by
  unfold upI
  split_ifs with hs
  · exact incl_heatUp h (sub_pos.2 hs) (G s)
  · simp

lemma incl_duhUp {m m' : ℕ} (h : m' ≤ m) {G : ℝ → Hm m} (hG : Continuous G)
    {t : ℝ} (ht : 0 ≤ t) :
    incl (Nat.succ_le_succ h) (duhUp m G t) = duhUp m' (fun s => incl h (G s)) t := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_Icc hG 0 t
  unfold duhUp
  have hint := intervalIntegrable_upI hG ht hM0 hM
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm (incl (Nat.succ_le_succ h)) hint]
  exact intervalIntegral.integral_congr fun s _ => incl_upI h G t s

lemma incl_scaleG {m m' : ℕ} (h : m' ≤ m) (ν : ℝ) (G : ℝ → Hm m) (σ : ℝ) :
    incl h (scaleG ν G σ) = scaleG ν (fun s => incl h (G s)) σ := by
  simp only [scaleG, map_smul]

lemma incl_duhν {m m' : ℕ} (h : m' ≤ m) {ν t : ℝ} (hνt : 0 ≤ ν * t)
    {G : ℝ → Hm m} (hG : Continuous G) :
    incl (Nat.succ_le_succ h) (duhν m ν G t) = duhν m' ν (fun s => incl h (G s)) t := by
  unfold duhν
  rw [incl_duhUp h (continuous_scaleG hG) hνt]
  refine congrArg (fun H => duhUp m' H (ν * t)) (funext fun σ => incl_scaleG h ν G σ)

lemma incl_eq_rec {m n m' : ℕ} (e : m = n) (hn : m' ≤ n) (hm : m' ≤ m) (x : Hm m) :
    incl hn (e ▸ x) = incl hm x := by
  cases e
  rw [Subsingleton.elim hn hm]

lemma three_le_pred_succ (hk : 2 ≤ k) : 3 ≤ (k + 1) - 1 + 1 := by
  simpa [pred_succ_eq hk] using three_le_succ hk

lemma incl_duhHigh (hk : 2 ≤ k) {ν t : ℝ} (hνt : 0 ≤ ν * t)
    {G : ℝ → Hm ((k + 1) - 1)} (hG : Continuous G) :
    incl (three_le_succ hk) (duhHigh hk ν G t) =
      duhν 2 ν (fun s => incl (le_pred_of_succ hk) (G s)) t := by
  unfold duhHigh
  rw [incl_eq_rec (pred_succ_eq hk) (three_le_succ hk) (three_le_pred_succ hk)]
  exact incl_duhν (le_pred_of_succ hk) hνt hG

/-- Pointwise cocycle identity for the smoothing integrand, valid for `s < t0`. -/
lemma upI_cocycle {m : ℕ} {G : ℝ → Hm m} {t0 τ s : ℝ} (hτ : 0 < τ) (hs : s < t0) :
    upI G (t0 + τ) s = heatH (m + 1) τ (upI G t0 s) := by
  have h1 : s < t0 + τ := by linarith
  have h2 : 0 < t0 - s := sub_pos.2 hs
  have h3 : 0 < t0 + τ - s := by linarith
  unfold upI
  rw [dif_pos h1, dif_pos hs]
  have hle : t0 - s ≤ t0 + τ - s := by linarith
  convert heatUp_eq h2 h3 hle (G s) using 2
  ring

lemma heatUp_congr {m : ℕ} {τ τ' : ℝ} (hτ : 0 < τ) (hτ' : 0 < τ')
    (e : τ = τ') (G : Hm m) : heatUp m hτ G = heatUp m hτ' G := by
  cases e; rfl

lemma upI_shift {m : ℕ} {G : ℝ → Hm m} (t0 τ σ : ℝ) :
    upI G (t0 + τ) (σ + t0) = upI (fun s => G (s + t0)) τ σ := by
  unfold upI
  have : σ + t0 < t0 + τ ↔ σ < τ := by constructor <;> intro <;> linarith
  split_ifs with h1 h2 h3
  · have htime : t0 + τ - (σ + t0) = τ - σ := by ring
    exact heatUp_congr (sub_pos.2 h1) (sub_pos.2 h2) htime (G (σ + t0))
  · exact (h2 (this.1 h1)).elim
  · exact (h1 (this.2 h3)).elim
  · rfl

/-- Duhamel cocycle:
`∫₀^{t0+τ} e^{(t0+τ-s)Δ} G(s) ds = e^{τΔ} (∫₀^{t0} e^{(t0-s)Δ} G(s) ds) + ∫₀^τ e^{(τ-σ)Δ} G(σ+t0) dσ`. -/
theorem duhUp_cocycle {m : ℕ} {G : ℝ → Hm m} (hG : Continuous G) {t0 τ : ℝ}
    (ht0 : 0 ≤ t0) (hτ : 0 ≤ τ) :
    duhUp m G (t0 + τ) =
      heatH (m + 1) τ (duhUp m G t0) + duhUp m (fun s => G (s + t0)) τ := by
  rcases eq_or_lt_of_le hτ with hτ0 | hτpos
  · rw [← hτ0, add_zero, heatH_zero]
    unfold duhUp
    rw [intervalIntegral.integral_same, add_zero]
  obtain ⟨M, hM0, hM⟩ := exists_bound_Icc hG 0 (t0 + τ)
  have hsum : 0 ≤ t0 + τ := add_nonneg ht0 hτ
  have hint : IntervalIntegrable (upI G (t0 + τ)) volume 0 (t0 + τ) :=
    intervalIntegrable_upI hG hsum hM0 hM
  have h1 : IntervalIntegrable (upI G (t0 + τ)) volume 0 t0 :=
    hint.mono_set (by
      rw [uIcc_of_le ht0, uIcc_of_le hsum]
      exact Icc_subset_Icc le_rfl (le_add_of_nonneg_right hτ))
  have h2 : IntervalIntegrable (upI G (t0 + τ)) volume t0 (t0 + τ) :=
    hint.mono_set (by
      rw [uIcc_of_le (le_add_of_nonneg_right hτ), uIcc_of_le hsum]
      exact Icc_subset_Icc ht0 le_rfl)
  have hMt0 : ∀ s ∈ Icc 0 t0, ‖G s‖ ≤ M := fun s hs =>
    hM s ⟨hs.1, hs.2.trans (le_add_of_nonneg_right hτ)⟩
  unfold duhUp
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have e1 : (∫ s in (0 : ℝ)..t0, upI G (t0 + τ) s) =
      heatH (m + 1) τ (∫ s in (0 : ℝ)..t0, upI G t0 s) := by
    have hI0 := intervalIntegrable_upI hG ht0 hM0 hMt0
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm (heatH (m + 1) τ) hI0]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_singleton (μ := volume) t0)]
      with s hs0 hs
    have hs' : s ∈ uIoc 0 t0 := hs
    rw [uIoc_of_le ht0] at hs'
    have hslt : s < t0 := lt_of_le_of_ne hs'.2 hs0
    exact upI_cocycle hτpos hslt
  have e2 : (∫ s in t0..(t0 + τ), upI G (t0 + τ) s) =
      ∫ σ in (0 : ℝ)..τ, upI (fun s => G (s + t0)) τ σ := by
    have hlim : (∫ s in t0..(t0 + τ), upI G (t0 + τ) s) =
        ∫ s in (0 + t0)..(τ + t0), upI G (t0 + τ) s := by
      rw [zero_add, add_comm t0 τ]
    rw [hlim, ← intervalIntegral.integral_comp_add_right (fun s => upI G (t0 + τ) s) t0]
    exact intervalIntegral.integral_congr fun σ _ => upI_shift t0 τ σ
  rw [e1, e2]

theorem duhν_cocycle {m : ℕ} {ν : ℝ} (hν : 0 < ν) {G : ℝ → Hm m} (hG : Continuous G)
    {t0 τ : ℝ} (ht0 : 0 ≤ t0) (hτ : 0 ≤ τ) :
    duhν m ν G (t0 + τ) =
      heatH (m + 1) (ν * τ) (duhν m ν G t0) + duhν m ν (fun s => G (s + t0)) τ := by
  unfold duhν
  rw [mul_add, duhUp_cocycle (continuous_scaleG hG) (mul_nonneg hν.le ht0) (mul_nonneg hν.le hτ)]
  have hsh : (fun σ => scaleG ν G (σ + ν * t0)) = scaleG ν (fun s => G (s + t0)) := by
    funext σ
    simp only [scaleG, add_div, mul_div_cancel_left₀ _ hν.ne']
  rw [hsh]

lemma eq_rec_add {m n : ℕ} (e : m = n) (x y : Hm m) :
    e ▸ (x + y) = (e ▸ x) + (e ▸ y) := by
  cases e; rfl

lemma eq_rec_heatH {m n : ℕ} (e : m = n) (τ : ℝ) (x : Hm m) :
    e ▸ heatH m τ x = heatH n τ (e ▸ x) := by
  cases e; rfl

theorem duhHigh_cocycle (hk : 2 ≤ k) {ν : ℝ} (hν : 0 < ν)
    {G : ℝ → Hm ((k + 1) - 1)} (hG : Continuous G)
    {t0 τ : ℝ} (ht0 : 0 ≤ t0) (hτ : 0 ≤ τ) :
    duhHigh hk ν G (t0 + τ) =
      heatH (k + 1) (ν * τ) (duhHigh hk ν G t0) +
        duhHigh hk ν (fun s => G (s + t0)) τ := by
  unfold duhHigh
  rw [duhν_cocycle (m := (k + 1) - 1) hν hG ht0 hτ]
  cases (pred_succ_eq hk)
  rfl

/-! ## Inclusion of paths, and identification on the min of the two local times -/

def inclMap (hk : 2 ≤ k) {T : ℝ} (u : XTs k T) : XT T :=
  ContinuousMap.mk (fun t => incl (three_le_succ hk) (u t))
    ((incl (three_le_succ hk)).continuous.comp u.continuous)

lemma incl_IccExtend (hk : 2 ≤ k) {T : ℝ} (hT : 0 ≤ T) (u : XTs k T) (s : ℝ) :
    incl (three_le_succ hk) (ContinuousMap.IccExtend hT u s) =
      ContinuousMap.IccExtend hT (inclMap hk u) s :=
  rfl

lemma incl_mildFnS (hk : 2 ≤ k) {ν T t : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (ht : 0 ≤ t)
    (u₀ : Hm (k + 1)) (u : XTs k T) :
    incl (three_le_succ hk) (mildFnS hk ν u₀ hT u t) =
      mildFn ν (incl (three_le_succ hk) u₀) hT (inclMap hk u) t := by
  unfold mildFnS mildFn
  rw [map_sub, incl_heatH hk]
  have hνt : 0 ≤ ν * t := mul_nonneg hν.le ht
  have hNS : Continuous
      (fun s => NSN (three_le_succ hk) ((ContinuousMap.IccExtend hT u) s)) :=
    continuous_NSN_extUS hk hT u
  rw [incl_duhHigh hk hνt hNS]
  refine congrArg (fun H => heatH 3 (ν * t) (incl (three_le_succ hk) u₀) - duhν 2 ν H t)
    (funext fun s => ?_)
  rw [incl_NSN hk, incl_IccExtend hk hT u]

lemma incl_PhiS (hk : 2 ≤ k) {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (u₀ : Hm (k + 1))
    (u : XTs k T) :
    inclMap hk (PhiS hk hν hT u₀ u) = Phi hν hT (incl (three_le_succ hk) u₀) (inclMap hk u) := by
  refine ContinuousMap.ext fun t => ?_
  simp only [inclMap, ContinuousMap.coe_mk, coe_PhiS, coe_Phi]
  exact incl_mildFnS hk hν hT t.2.1 u₀ u

lemma inclMap_const (hk : 2 ≤ k) {T : ℝ} (u₀ : Hm (k + 1)) :
    inclMap hk (const (Icc (0 : ℝ) T) u₀) =
      const (Icc (0 : ℝ) T) (incl (three_le_succ hk) u₀) :=
  rfl

lemma inclMap_iterate (hk : 2 ≤ k) {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (u₀ : Hm (k + 1)) (n : ℕ) (u : XTs k T) :
    inclMap hk ((PhiS hk hν hT u₀)^[n] u) =
      (Phi hν hT (incl (three_le_succ hk) u₀))^[n] (inclMap hk u) := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', incl_PhiS, ih]

lemma visc_le_of_le_localTimeS {ν T : ℝ} (hν : 0 < ν) (u₀ : Hm (k + 1))
    (hT : 0 ≤ T) (hle : T ≤ localTimeS ν u₀) :
    T + 2 * Real.sqrt (T / ν) ≤ deltaS u₀ :=
  (visc_time_mono hν hle hT).trans (localTimeS_visc hν u₀)

lemma visc_le_of_le_localTime {ν T : ℝ} (hν : 0 < ν) (u₀ : Hm 3)
    (hT : 0 ≤ T) (hle : T ≤ localTime ν u₀) :
    T + 2 * Real.sqrt (T / ν) ≤ delta u₀ :=
  (visc_time_mono hν hle hT).trans (localTime_visc hν u₀)

theorem local_mildS_on (hk : 2 ≤ k) {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (u₀ : Hm (k + 1)) (hTδ : T + 2 * Real.sqrt (T / ν) ≤ deltaS u₀) :
    ∃ u : XTs k T, u ∈ closedBall (0 : XTs k T) (radS u₀) ∧
      IsMildS hk hT ν u₀ u ∧
      Tendsto (fun n => (PhiS hk hν hT u₀)^[n] (const (Icc (0 : ℝ) T) u₀))
        atTop (𝓝 u) ∧
      ∀ v ∈ closedBall (0 : XTs k T) (radS u₀),
        IsMildS hk hT ν u₀ v → v = u := by
  have hsc : IsComplete (closedBall (0 : XTs k T) (radS u₀)) := isClosed_closedBall.isComplete
  have hsf := mapsTo_PhiS hk hν hT u₀ hTδ
  have hf := contracting_PhiS hk hν hT u₀ hTδ
  have hx : const (Icc (0 : ℝ) T) u₀ ∈ closedBall (0 : XTs k T) (radS u₀) :=
    const_mem_ballS hT u₀
  have he : edist (const (Icc (0 : ℝ) T) u₀)
      (PhiS hk hν hT u₀ (const (Icc (0 : ℝ) T) u₀)) ≠ ⊤ := (edist_lt_top _ _).ne
  obtain ⟨u, hu, hfix, hlim, _⟩ := hf.exists_fixedPoint' hsc hsf hx he
  refine ⟨u, hu, (isMildS_iff_fixed hk hν hT u₀ u).2 (by exact hfix), hlim, ?_⟩
  intro v hv hvM
  exact unique_mildS_in_ball hk hν hT u₀ hTδ hv hu hvM
    ((isMildS_iff_fixed hk hν hT u₀ u).2 (by exact hfix))

theorem local_mild_on {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (u₀ : Hm 3)
    (hTδ : T + 2 * Real.sqrt (T / ν) ≤ delta u₀) :
    ∃ u : XT T, u ∈ closedBall (0 : XT T) (rad u₀) ∧
      IsMild hT ν u₀ u ∧
      Tendsto (fun n => (Phi hν hT u₀)^[n] (const (Icc (0 : ℝ) T) u₀))
        atTop (𝓝 u) ∧
      ∀ v ∈ closedBall (0 : XT T) (rad u₀), IsMild hT ν u₀ v → v = u := by
  have hsc : IsComplete (closedBall (0 : XT T) (rad u₀)) := isClosed_closedBall.isComplete
  have hsf := mapsTo_Phi hν hT u₀ hTδ
  have hf := contracting_Phi hν hT u₀ hTδ
  have hx : const (Icc (0 : ℝ) T) u₀ ∈ closedBall (0 : XT T) (rad u₀) := const_mem_ball hT u₀
  have he : edist (const (Icc (0 : ℝ) T) u₀)
      (Phi hν hT u₀ (const (Icc (0 : ℝ) T) u₀)) ≠ ⊤ := (edist_lt_top _ _).ne
  obtain ⟨u, hu, hfix, hlim, _⟩ := hf.exists_fixedPoint' hsc hsf hx he
  refine ⟨u, hu, (isMild_iff_fixed hν hT u₀ u).2 (by exact hfix), hlim, ?_⟩
  intro v hv hvM
  exact unique_mild_in_ball hν hT u₀ hTδ hv hu hvM
    ((isMild_iff_fixed hν hT u₀ u).2 (by exact hfix))

lemma continuous_inclMap (hk : 2 ≤ k) {T : ℝ} :
    Continuous (inclMap hk : XTs k T → XT T) := by
  refine LipschitzWith.continuous (LipschitzWith.of_dist_le_mul (K := 1) fun u v => ?_)
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
  refine (ContinuousMap.norm_le (inclMap hk u - inclMap hk v) (norm_nonneg (u - v))).2 fun t => ?_
  have : (inclMap hk u - inclMap hk v) t = incl (three_le_succ hk) ((u - v) t) := by
    simp [inclMap, map_sub]
  rw [this]
  exact (norm_incl_le (three_le_succ hk) _).trans (norm_coe_le_norm (u - v) t)

/-- On the min of the Ĥ^{k+1} and Ĥ³ local times, the included Ĥ^{k+1} mild
solution is the Ĥ³ mild solution. -/
theorem persist_on_minTime (hk : 2 ≤ k) {ν : ℝ} (hν : 0 < ν) (u₀ : Hm (k + 1)) :
    let T := min (localTimeS ν u₀) (localTime ν (incl (three_le_succ hk) u₀))
    0 < T ∧
      ∃ u : XTs k T,
        u ∈ closedBall (0 : XTs k T) (radS u₀) ∧
        IsMildS hk (le_min (localTimeS_nonneg hν u₀)
          (localTime_nonneg hν (incl (three_le_succ hk) u₀))) ν u₀ u ∧
        inclMap hk u ∈ closedBall (0 : XT T) (rad (incl (three_le_succ hk) u₀)) ∧
        IsMild (le_min (localTimeS_nonneg hν u₀)
          (localTime_nonneg hν (incl (three_le_succ hk) u₀))) ν
          (incl (three_le_succ hk) u₀) (inclMap hk u) := by
  set T := min (localTimeS ν u₀) (localTime ν (incl (three_le_succ hk) u₀))
  have hT : 0 ≤ T := le_min (localTimeS_nonneg hν u₀)
    (localTime_nonneg hν (incl (three_le_succ hk) u₀))
  have hTpos : 0 < T := lt_min (localTimeS_pos hν u₀)
    (localTime_pos hν (incl (three_le_succ hk) u₀))
  have hTδS : T + 2 * Real.sqrt (T / ν) ≤ deltaS u₀ :=
    visc_le_of_le_localTimeS hν u₀ hT (min_le_left _ _)
  have hTδ3 : T + 2 * Real.sqrt (T / ν) ≤ delta (incl (three_le_succ hk) u₀) :=
    visc_le_of_le_localTime hν _ hT (min_le_right _ _)
  obtain ⟨u, hu, huM, hlimS, _⟩ := local_mildS_on hk hν hT u₀ hTδS
  obtain ⟨v, hv, hvM, hlim3, _⟩ :=
    local_mild_on hν hT (incl (three_le_succ hk) u₀) hTδ3
  have hcomm : ∀ n,
      inclMap hk ((PhiS hk hν hT u₀)^[n] (const (Icc (0 : ℝ) T) u₀)) =
        (Phi hν hT (incl (three_le_succ hk) u₀))^[n]
          (const (Icc (0 : ℝ) T) (incl (three_le_succ hk) u₀)) := fun n => by
    rw [inclMap_iterate, inclMap_const]
  have htend : Tendsto (fun n =>
      (Phi hν hT (incl (three_le_succ hk) u₀))^[n]
        (const (Icc (0 : ℝ) T) (incl (three_le_succ hk) u₀))) atTop (𝓝 (inclMap hk u)) := by
    have := (continuous_inclMap hk).continuousAt.tendsto.comp hlimS
    exact this.congr fun n => hcomm n
  have : inclMap hk u = v := tendsto_nhds_unique htend hlim3
  refine ⟨hTpos, u, hu, huM, this ▸ hv, this ▸ hvM⟩

#print axioms PersistenceHm.incl_duhHigh
#print axioms PersistenceHm.duhHigh_cocycle
#print axioms PersistenceHm.persist_on_minTime


/-! ## Restriction, shift, glue, and the R₃ a priori bound -/

lemma duhUp_congr {m : ℕ} {G H : ℝ → Hm m} {t : ℝ} (ht : 0 ≤ t)
    (h : ∀ s ∈ Icc 0 t, G s = H s) : duhUp m G t = duhUp m H t := by
  unfold duhUp
  refine intervalIntegral.integral_congr fun s hs => ?_
  have hs' : s ∈ Icc 0 t := by rwa [uIcc_of_le ht] at hs
  unfold upI
  split_ifs
  · rw [h s hs']
  · rfl

lemma duhν_congr {m : ℕ} {ν t : ℝ} (hν : 0 < ν) (ht : 0 ≤ t)
    {G H : ℝ → Hm m} (h : ∀ s ∈ Icc 0 t, G s = H s) :
    duhν m ν G t = duhν m ν H t := by
  unfold duhν
  refine duhUp_congr (mul_nonneg hν.le ht) fun σ hσ => ?_
  simp only [scaleG]
  have hs : σ / ν ∈ Icc 0 t := by
    constructor
    · exact div_nonneg hσ.1 hν.le
    · exact (div_le_iff₀ hν).2 (by simpa [mul_comm] using hσ.2)
  rw [h _ hs]

lemma duhHigh_congr (hk : 2 ≤ k) {ν t : ℝ} (hν : 0 < ν) (ht : 0 ≤ t)
    {G H : ℝ → Hm ((k + 1) - 1)} (h : ∀ s ∈ Icc 0 t, G s = H s) :
    duhHigh hk ν G t = duhHigh hk ν H t := by
  unfold duhHigh
  rw [duhν_congr hν ht h]

def restrictXTs (hk : 2 ≤ k) {T T' : ℝ} (h : T' ≤ T) (u : XTs k T) : XTs k T' :=
  ContinuousMap.mk
    (fun t => u ⟨t.1, ⟨t.2.1, le_trans t.2.2 h⟩⟩)
    (u.continuous.comp
      (Continuous.subtype_mk continuous_subtype_val fun t => ⟨t.2.1, t.2.2.trans h⟩))

lemma IccExtend_restrict (hk : 2 ≤ k) {T T' : ℝ} (hT : 0 ≤ T) (hT' : 0 ≤ T')
    (h : T' ≤ T) (u : XTs k T) {s : ℝ} (hs : s ∈ Icc 0 T') :
    ContinuousMap.IccExtend hT' (restrictXTs hk h u) s =
      ContinuousMap.IccExtend hT u s := by
  rw [ContinuousMap.coe_IccExtend, ContinuousMap.coe_IccExtend,
    Set.IccExtend_of_mem (hx := hs),
    Set.IccExtend_of_mem (hx := ⟨hs.1, hs.2.trans h⟩)]
  rfl

lemma isMildS_restrict (hk : 2 ≤ k) {ν T T' : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (hT' : 0 ≤ T') (h : T' ≤ T) (u₀ : Hm (k + 1)) {u : XTs k T}
    (hu : IsMildS hk hT ν u₀ u) :
    IsMildS hk hT' ν u₀ (restrictXTs hk h u) := by
  intro t
  have htT : (t : ℝ) ≤ T := t.2.2.trans h
  have huv := hu ⟨t.1, ⟨t.2.1, htT⟩⟩
  have hpt : restrictXTs hk h u t = u ⟨t.1, ⟨t.2.1, htT⟩⟩ := rfl
  rw [hpt, huv]
  have hsrc : ∀ s ∈ Icc 0 (t : ℝ),
      NSN (three_le_succ hk) ((ContinuousMap.IccExtend hT u) s) =
        NSN (three_le_succ hk)
          ((ContinuousMap.IccExtend hT' (restrictXTs hk h u)) s) := fun s hs => by
    have hs' : s ∈ Icc 0 T' := ⟨hs.1, hs.2.trans t.2.2⟩
    rw [IccExtend_restrict hk hT hT' h u hs']
  rw [duhHigh_congr hk hν t.2.1 hsrc]

lemma shift_time_mem {T t0 τ s : ℝ} (ht0 : 0 ≤ t0) (hsum : t0 + τ ≤ T)
    (hs : s ∈ Icc 0 τ) : s + t0 ∈ Icc 0 T := by
  constructor
  · linarith [hs.1]
  · linarith [hs.2, hsum]

def shiftXTs (hk : 2 ≤ k) {T t0 τ : ℝ} (ht0 : 0 ≤ t0) (hτ : 0 ≤ τ)
    (hsum : t0 + τ ≤ T) (u : XTs k T) : XTs k τ :=
  ContinuousMap.mk
    (fun σ => u ⟨σ.1 + t0, shift_time_mem ht0 hsum σ.2⟩)
    (u.continuous.comp
      (Continuous.subtype_mk
        (continuous_subtype_val.add (continuous_const : Continuous (fun _ : Icc (0 : ℝ) τ => t0)))
        fun σ => shift_time_mem ht0 hsum σ.2))

lemma IccExtend_shift (hk : 2 ≤ k) {T t0 τ : ℝ} (hT : 0 ≤ T) (ht0 : 0 ≤ t0)
    (hτ : 0 ≤ τ) (hsum : t0 + τ ≤ T) (u : XTs k T) {s : ℝ}
    (hs : s ∈ Icc 0 τ) :
    ContinuousMap.IccExtend hτ (shiftXTs hk ht0 hτ hsum u) s =
      ContinuousMap.IccExtend hT u (s + t0) := by
  have hsT : s + t0 ∈ Icc 0 T := shift_time_mem ht0 hsum hs
  rw [ContinuousMap.coe_IccExtend, ContinuousMap.coe_IccExtend,
    Set.IccExtend_of_mem (hx := hs), Set.IccExtend_of_mem (hx := hsT)]
  apply congrArg u
  ext
  rfl

lemma isMildS_shift (hk : 2 ≤ k) {ν T t0 τ : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (ht0 : 0 ≤ t0) (hτ : 0 ≤ τ) (hsum : t0 + τ ≤ T)
    (u₀ : Hm (k + 1)) {u : XTs k T} (hu : IsMildS hk hT ν u₀ u) :
    IsMildS hk hτ ν (u ⟨t0, ⟨ht0, le_trans (le_add_of_nonneg_right hτ) hsum⟩⟩)
      (shiftXTs hk ht0 hτ hsum u) := by
  intro σ
  have hpt : ((σ : ℝ) + t0) ∈ Icc 0 T := shift_time_mem ht0 hsum σ.2
  have huσ := hu ⟨(σ : ℝ) + t0, hpt⟩
  have hu0 := hu ⟨t0, ⟨ht0, le_trans (le_add_of_nonneg_right hτ) hsum⟩⟩
  have hsh : shiftXTs hk ht0 hτ hsum u σ = u ⟨(σ : ℝ) + t0, hpt⟩ := by
    apply congrArg u
    ext
    rfl
  rw [hsh, huσ]
  have hN : Continuous
      (fun s => NSN (three_le_succ hk) ((ContinuousMap.IccExtend hT u) s)) :=
    continuous_NSN_extUS hk hT u
  have htime : (σ : ℝ) + t0 = t0 + (σ : ℝ) := add_comm _ _
  simp only [htime]
  rw [duhHigh_cocycle hk hν hN ht0 σ.2.1]
  have hheat : heatH (k + 1) (ν * (t0 + (σ : ℝ))) u₀ =
      heatH (k + 1) (ν * (σ : ℝ)) (heatH (k + 1) (ν * t0) u₀) := by
    rw [mul_add, add_comm (ν * t0)]
    exact (heatH_heatH (mul_nonneg hν.le σ.2.1) (mul_nonneg hν.le ht0) u₀).symm
  rw [hheat, hu0, map_sub]
  have hsrc : ∀ s ∈ Icc 0 (σ : ℝ),
      NSN (three_le_succ hk) ((ContinuousMap.IccExtend hT u) (s + t0)) =
        NSN (three_le_succ hk)
          ((ContinuousMap.IccExtend hτ (shiftXTs hk ht0 hτ hsum u)) s) := fun s hs => by
    have hsτ : s ∈ Icc 0 τ := ⟨hs.1, hs.2.trans σ.2.2⟩
    rw [IccExtend_shift hk hT ht0 hτ hsum u hsτ]
  rw [duhHigh_congr hk hν σ.2.1 hsrc]
  abel

#print axioms PersistenceHm.isMildS_restrict
#print axioms PersistenceHm.isMildS_shift


/-! ## A priori doubling on windows controlled only by an Ĥ³ radius -/

lemma isMild_inclMap (hk : 2 ≤ k) {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (u₀ : Hm (k + 1)) {u : XTs k T} (hu : IsMildS hk hT ν u₀ u) :
    IsMild hT ν (incl (three_le_succ hk) u₀) (inclMap hk u) := by
  intro t
  have h := hu t
  have hpt : inclMap hk u t = incl (three_le_succ hk) (u t) := rfl
  rw [hpt, h]
  exact incl_mildFnS hk hν hT t.2.1 u₀ u

def deltaPersist (k : ℕ) (R3 : ℝ) : ℝ :=
  1 / (2 * (18 * Cm (k + 1) * max R3 0 + 1))

lemma denPersist_pos (k : ℕ) (R3 : ℝ) :
    0 < 2 * (18 * Cm (k + 1) * max R3 0 + 1) :=
  mul_pos (by norm_num)
    (add_pos_of_nonneg_of_pos (mul_nonneg (Cm18_nonneg k) (le_max_right _ _)) one_pos)

lemma deltaPersist_pos (k : ℕ) (R3 : ℝ) : 0 < deltaPersist k R3 :=
  one_div_pos.2 (denPersist_pos k R3)

def timePersist (k : ℕ) (ν R3 : ℝ) : ℝ := timeSlot ν (deltaPersist k R3)

lemma timePersist_pos {ν : ℝ} (hν : 0 < ν) (k : ℕ) (R3 : ℝ) :
    0 < timePersist k ν R3 :=
  timeSlot_pos hν (deltaPersist_pos k R3)

lemma timePersist_nonneg {ν : ℝ} (hν : 0 < ν) (k : ℕ) (R3 : ℝ) :
    0 ≤ timePersist k ν R3 :=
  (timePersist_pos hν k R3).le

lemma timePersist_visc {ν : ℝ} (hν : 0 < ν) (k : ℕ) (R3 : ℝ) :
    timePersist k ν R3 + 2 * Real.sqrt (timePersist k ν R3 / ν) ≤
      deltaPersist k R3 :=
  timeSlot_visc hν (deltaPersist_pos k R3) (timePersist_nonneg hν k R3) le_rfl

lemma visc_le_of_le_timePersist {ν T R3 : ℝ} (hν : 0 < ν) (k : ℕ)
    (hT : 0 ≤ T) (hle : T ≤ timePersist k ν R3) :
    T + 2 * Real.sqrt (T / ν) ≤ deltaPersist k R3 :=
  (visc_time_mono hν hle hT).trans (timePersist_visc hν k R3)

lemma persist_const_le_half (k : ℕ) {R3 : ℝ} (hR3 : 0 ≤ R3) :
    18 * Cm (k + 1) * R3 * deltaPersist k R3 ≤ 1 / 2 := by
  unfold deltaPersist
  have hmax : max R3 0 = R3 := max_eq_left hR3
  rw [hmax]
  set a := 18 * Cm (k + 1) * R3
  have ha : 0 ≤ a := mul_nonneg (Cm18_nonneg k) hR3
  have hden : 0 < 2 * (a + 1) := mul_pos (by norm_num) (add_pos_of_nonneg_of_pos ha one_pos)
  change a * (1 / (2 * (a + 1))) ≤ 1 / 2
  rw [mul_one_div]
  refine (div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 2)).2 ?_
  linarith

lemma norm_NSN_ext_le_R3 (hk : 2 ≤ k) {T R3 : ℝ} (hT : 0 ≤ T) (hR3 : 0 ≤ R3)
    {u : XTs k T} (hbd : ∀ t : Icc 0 T, ‖incl (three_le_succ hk) (u t)‖ ≤ R3)
    (s : ℝ) (hs : s ∈ Icc 0 T) :
    ‖NSN (three_le_succ hk) ((ContinuousMap.IccExtend hT u) s)‖ ≤
      18 * Cm (k + 1) * ‖u‖ * R3 := by
  have hs' : s ∈ Icc 0 T := hs
  have : ContinuousMap.IccExtend hT u s = u ⟨s, hs'⟩ := by
    rw [ContinuousMap.coe_IccExtend, Set.IccExtend_of_mem (hx := hs')]
  rw [this]
  refine (norm_NSN_le (three_le_succ hk) (u ⟨s, hs'⟩)).trans ?_
  have hC : 0 ≤ 18 * Cm (k + 1) * ‖u ⟨s, hs'⟩‖ :=
    mul_nonneg (Cm18_nonneg k) (norm_nonneg _)
  have hin := (norm_incl_le (three_le_succ hk) (u ⟨s, hs'⟩))
  have hR : ‖incl (three_le_succ hk) (u ⟨s, hs'⟩)‖ ≤ R3 := hbd ⟨s, hs'⟩
  have hu : ‖u ⟨s, hs'⟩‖ ≤ ‖u‖ := norm_coe_le_norm u _
  refine (mul_le_mul_of_nonneg_left hR
      (mul_nonneg (Cm18_nonneg k) (norm_nonneg _))).trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hu (Cm18_nonneg k)) hR3

/-- If a mild Ĥ^{k+1} path lives on an interval no longer than the R₃-window
`timePersist`, and its included Ĥ³ values stay ≤ R₃, then
`‖u‖_{C_t Ĥ^{k+1}} ≤ 2 ‖u₀‖_{Ĥ^{k+1}}`. -/
theorem apriori_double (hk : 2 ≤ k) {ν T R3 : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (hR3 : 0 ≤ R3)
    (hTδ : T + 2 * Real.sqrt (T / ν) ≤ deltaPersist k R3)
    (u₀ : Hm (k + 1)) {u : XTs k T} (hu : IsMildS hk hT ν u₀ u)
    (hbd3 : ∀ t : Icc 0 T, ‖incl (three_le_succ hk) (u t)‖ ≤ R3) :
    ‖u‖ ≤ 2 * ‖u₀‖ := by
  have hM0 : 0 ≤ 18 * Cm (k + 1) * ‖u‖ * R3 :=
    mul_nonneg (mul_nonneg (Cm18_nonneg k) (norm_nonneg _)) hR3
  have hpt : ∀ t : Icc 0 T, ‖u t‖ ≤
      ‖u₀‖ + (18 * Cm (k + 1) * ‖u‖ * R3) * (T + 2 * Real.sqrt (T / ν)) := fun t => by
    have := hu t
    rw [this]
    refine (norm_sub_le _ _).trans (add_le_add (norm_heatH_le (k + 1) _ u₀) ?_)
    have hN := continuous_NSN_extUS hk hT u
    have hbd : ∀ s ∈ Icc 0 (t : ℝ),
        ‖NSN (three_le_succ hk) ((ContinuousMap.IccExtend hT u) s)‖ ≤
          18 * Cm (k + 1) * ‖u‖ * R3 := fun s hs =>
      norm_NSN_ext_le_R3 hk hT hR3 hbd3 s ⟨hs.1, hs.2.trans t.2.2⟩
    refine (norm_duhHigh_le hk hν hN t.2.1 hM0 hbd).trans ?_
    exact mul_le_mul_of_nonneg_left (visc_time_mono hν t.2.2 t.2.1) hM0
  have hnorm : ‖u‖ ≤
      ‖u₀‖ + (18 * Cm (k + 1) * ‖u‖ * R3) * (T + 2 * Real.sqrt (T / ν)) :=
    (ContinuousMap.norm_le u (by
      have := add_nonneg (norm_nonneg u₀)
        (mul_nonneg hM0 (visc_nonneg hν hT))
      exact this)).2 hpt
  have hstep : ‖u‖ ≤
      ‖u₀‖ + (18 * Cm (k + 1) * ‖u‖ * R3) * deltaPersist k R3 :=
    hnorm.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hTδ hM0))
  have hhalf :
      (18 * Cm (k + 1) * ‖u‖ * R3) * deltaPersist k R3 ≤ (1 / 2) * ‖u‖ := by
    have : 18 * Cm (k + 1) * R3 * deltaPersist k R3 * ‖u‖ ≤
        (1 / 2) * ‖u‖ :=
      mul_le_mul_of_nonneg_right (persist_const_le_half k hR3) (norm_nonneg _)
    convert this using 1; ring
  have : ‖u‖ ≤ ‖u₀‖ + (1 / 2) * ‖u‖ := hstep.trans (add_le_add le_rfl hhalf)
  linarith

#print axioms PersistenceHm.apriori_double
#print axioms PersistenceHm.isMild_inclMap


/-! ## Gluing, chunk bounds, and persistence on the Ĥ³ local time -/

lemma timeSlot_mono {ν ε ε' : ℝ} (hν : 0 ≤ ν) (hε : 0 ≤ ε) (h : ε ≤ ε') :
    timeSlot ν ε ≤ timeSlot ν ε' := by
  unfold timeSlot
  have h1 : ε / 2 ≤ ε' / 2 := by linarith
  have h2 : ν * (ε / 4) ^ 2 ≤ ν * (ε' / 4) ^ 2 := by
    refine mul_le_mul_of_nonneg_left ?_ hν
    exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  exact min_le_min h1 h2

lemma localTimeS_anti_norm {ν : ℝ} (hν : 0 < ν) {u v : Hm (k + 1)}
    (h : ‖u‖ ≤ ‖v‖) : localTimeS ν v ≤ localTimeS ν u := by
  unfold localTimeS deltaS radS
  have hδ : (1 / (2 * (36 * Cm (k + 1) * (2 * ‖v‖ + 1) + 1))) ≤
      1 / (2 * (36 * Cm (k + 1) * (2 * ‖u‖ + 1) + 1)) := by
    refine one_div_le_one_div_of_le (denS_pos u) ?_
    have : 36 * Cm (k + 1) * (2 * ‖u‖ + 1) ≤ 36 * Cm (k + 1) * (2 * ‖v‖ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [norm_nonneg u]) (Cm36_nonneg k)
    linarith
  exact timeSlot_mono hν.le (deltaS_pos v).le hδ

lemma duhHigh_zero (hk : 2 ≤ k) (ν : ℝ) (G : ℝ → Hm ((k + 1) - 1)) :
    duhHigh hk ν G 0 = 0 := by
  unfold duhHigh
  rw [duhν_zero]
  cases (pred_succ_eq hk)
  rfl

lemma eq_zero_of_isMildS (hk : 2 ≤ k) {ν : ℝ} (u₀ : Hm (k + 1))
    {u : XTs k 0} (hu : IsMildS hk le_rfl ν u₀ u) :
    u ⟨0, ⟨le_rfl, le_rfl⟩⟩ = u₀ := by
  have h := hu ⟨0, ⟨le_rfl, le_rfl⟩⟩
  simpa [heatH_zero, duhHigh_zero hk, sub_zero] using h

def glueXTs (hk : 2 ≤ k) {t0 τ : ℝ} (ht0 : 0 ≤ t0) (hτ : 0 ≤ τ)
    (u : XTs k t0) (v : XTs k τ)
    (hmatch : v ⟨0, ⟨le_rfl, hτ⟩⟩ = u ⟨t0, ⟨ht0, le_rfl⟩⟩) :
    XTs k (t0 + τ) :=
  ContinuousMap.mk
    (fun t =>
      if (t : ℝ) ≤ t0 then u (projIcc 0 t0 ht0 t.1)
      else v (projIcc 0 τ hτ (t.1 - t0)))
    (Continuous.if_le
      (u.continuous.comp (continuous_projIcc.comp continuous_subtype_val))
      (v.continuous.comp
        (continuous_projIcc.comp (continuous_subtype_val.sub continuous_const)))
      continuous_subtype_val continuous_const
      (fun t ht => by
        have ht' : (t : ℝ) = t0 := ht
        simp only [ht', sub_self]
        rw [projIcc_of_mem (hx := right_mem_Icc.2 ht0)]
        rw [projIcc_of_mem (hx := left_mem_Icc.2 hτ)]
        exact hmatch.symm))

lemma glue_eval_le (hk : 2 ≤ k) {t0 τ : ℝ} (ht0 : 0 ≤ t0) (hτ : 0 ≤ τ)
    (u : XTs k t0) (v : XTs k τ)
    (hmatch : v ⟨0, ⟨le_rfl, hτ⟩⟩ = u ⟨t0, ⟨ht0, le_rfl⟩⟩)
    (t : Icc (0 : ℝ) (t0 + τ)) (ht : (t : ℝ) ≤ t0) :
    glueXTs hk ht0 hτ u v hmatch t = u ⟨t.1, ⟨t.2.1, ht⟩⟩ := by
  dsimp [glueXTs]
  rw [if_pos ht, projIcc_of_mem]

lemma glue_eval_gt (hk : 2 ≤ k) {t0 τ : ℝ} (ht0 : 0 ≤ t0) (hτ : 0 ≤ τ)
    (u : XTs k t0) (v : XTs k τ)
    (hmatch : v ⟨0, ⟨le_rfl, hτ⟩⟩ = u ⟨t0, ⟨ht0, le_rfl⟩⟩)
    (t : Icc (0 : ℝ) (t0 + τ)) (ht : t0 < (t : ℝ)) :
    glueXTs hk ht0 hτ u v hmatch t =
      v ⟨t.1 - t0, ⟨sub_nonneg.2 ht.le, by linarith [t.2.2]⟩⟩ := by
  dsimp [glueXTs]
  rw [if_neg (not_le.2 ht), projIcc_of_mem (hx := ⟨sub_nonneg.2 ht.le, by linarith [t.2.2]⟩)]

#print axioms PersistenceHm.glueXTs


lemma IccExtend_glue_le (hk : 2 ≤ k) {t0 τ : ℝ} (ht0 : 0 ≤ t0) (hτ : 0 ≤ τ)
    (u : XTs k t0) (v : XTs k τ)
    (hmatch : v ⟨0, ⟨le_rfl, hτ⟩⟩ = u ⟨t0, ⟨ht0, le_rfl⟩⟩)
    {s : ℝ} (hs : s ∈ Icc 0 t0) :
    ContinuousMap.IccExtend (add_nonneg ht0 hτ) (glueXTs hk ht0 hτ u v hmatch) s =
      ContinuousMap.IccExtend ht0 u s := by
  have hs' : s ∈ Icc 0 (t0 + τ) := ⟨hs.1, hs.2.trans (le_add_of_nonneg_right hτ)⟩
  rw [ContinuousMap.coe_IccExtend, ContinuousMap.coe_IccExtend,
    Set.IccExtend_of_mem (hx := hs'), Set.IccExtend_of_mem (hx := hs)]
  exact glue_eval_le hk ht0 hτ u v hmatch ⟨s, hs'⟩ hs.2

lemma IccExtend_glue_gt (hk : 2 ≤ k) {t0 τ : ℝ} (ht0 : 0 ≤ t0) (hτ : 0 ≤ τ)
    (u : XTs k t0) (v : XTs k τ)
    (hmatch : v ⟨0, ⟨le_rfl, hτ⟩⟩ = u ⟨t0, ⟨ht0, le_rfl⟩⟩)
    {s : ℝ} (hs0 : t0 ≤ s) (hs : s ∈ Icc 0 (t0 + τ)) :
    ContinuousMap.IccExtend (add_nonneg ht0 hτ) (glueXTs hk ht0 hτ u v hmatch) s =
      ContinuousMap.IccExtend hτ v (s - t0) := by
  have hsv : s - t0 ∈ Icc 0 τ := ⟨sub_nonneg.2 hs0, by linarith [hs.2]⟩
  rw [ContinuousMap.coe_IccExtend, ContinuousMap.coe_IccExtend,
    Set.IccExtend_of_mem (hx := hs), Set.IccExtend_of_mem (hx := hsv)]
  rcases eq_or_lt_of_le hs0 with h | h
  · subst h
    simp only [sub_self]
    have : glueXTs hk ht0 hτ u v hmatch ⟨t0, ⟨ht0, le_add_of_nonneg_right hτ⟩⟩ =
        u ⟨t0, ⟨ht0, le_rfl⟩⟩ :=
      glue_eval_le hk ht0 hτ u v hmatch _ le_rfl
    rw [this, ← hmatch]
  · exact glue_eval_gt hk ht0 hτ u v hmatch ⟨s, hs⟩ h

theorem isMildS_glue (hk : 2 ≤ k) {ν t0 τ : ℝ} (hν : 0 < ν)
    (ht0 : 0 ≤ t0) (hτ : 0 ≤ τ) (u₀ : Hm (k + 1))
    {u : XTs k t0} {v : XTs k τ}
    (hmatch : v ⟨0, ⟨le_rfl, hτ⟩⟩ = u ⟨t0, ⟨ht0, le_rfl⟩⟩)
    (hu : IsMildS hk ht0 ν u₀ u)
    (hv : IsMildS hk hτ ν (u ⟨t0, ⟨ht0, le_rfl⟩⟩) v) :
    IsMildS hk (add_nonneg ht0 hτ) ν u₀ (glueXTs hk ht0 hτ u v hmatch) := by
  intro t
  have hsumT : 0 ≤ t0 + τ := add_nonneg ht0 hτ
  rcases le_or_gt (t : ℝ) t0 with ht | ht
  · have huv := hu ⟨t.1, ⟨t.2.1, ht⟩⟩
    rw [glue_eval_le hk ht0 hτ u v hmatch t ht, huv]
    have hsrc : ∀ s ∈ Icc 0 (t : ℝ),
        NSN (three_le_succ hk) ((ContinuousMap.IccExtend ht0 u) s) =
          NSN (three_le_succ hk)
            ((ContinuousMap.IccExtend hsumT (glueXTs hk ht0 hτ u v hmatch)) s) :=
      fun s hs => by
        have hs0 : s ∈ Icc 0 t0 := ⟨hs.1, hs.2.trans ht⟩
        rw [IccExtend_glue_le hk ht0 hτ u v hmatch hs0]
    rw [duhHigh_congr hk hν t.2.1 hsrc]
  · have hσ : 0 ≤ (t : ℝ) - t0 := sub_nonneg.2 ht.le
    have hστ : (t : ℝ) - t0 ≤ τ := by linarith [t.2.2]
    have hvσ := hv ⟨(t : ℝ) - t0, ⟨hσ, hστ⟩⟩
    have hu0 := hu ⟨t0, ⟨ht0, le_rfl⟩⟩
    rw [glue_eval_gt hk ht0 hτ u v hmatch t ht, hvσ, hu0]
    have hN : Continuous
        (fun s => NSN (three_le_succ hk)
          ((ContinuousMap.IccExtend hsumT (glueXTs hk ht0 hτ u v hmatch)) s)) :=
      continuous_NSN_extUS hk hsumT _
    have hNu : Continuous
        (fun s => NSN (three_le_succ hk) ((ContinuousMap.IccExtend ht0 u) s)) :=
      continuous_NSN_extUS hk ht0 u
    have hsplit :=
      duhHigh_cocycle hk hν hN ht0 hσ
    have htval : t0 + ((t : ℝ) - t0) = (t : ℝ) := by ring
    have hheat : heatH (k + 1) (ν * (t : ℝ)) u₀ =
        heatH (k + 1) (ν * ((t : ℝ) - t0)) (heatH (k + 1) (ν * t0) u₀) := by
      have : ν * (t : ℝ) = ν * ((t : ℝ) - t0) + ν * t0 := by ring
      rw [this]
      exact (heatH_heatH (mul_nonneg hν.le hσ) (mul_nonneg hν.le ht0) u₀).symm
    -- express Duhamel of glue at t via the cocycle, then identify both pieces
    have hsrc0 : ∀ s ∈ Icc 0 t0,
        NSN (three_le_succ hk)
          ((ContinuousMap.IccExtend hsumT (glueXTs hk ht0 hτ u v hmatch)) s) =
          NSN (three_le_succ hk) ((ContinuousMap.IccExtend ht0 u) s) :=
      fun s hs => by rw [IccExtend_glue_le hk ht0 hτ u v hmatch hs]
    have hsrcσ : ∀ s ∈ Icc 0 ((t : ℝ) - t0),
        NSN (three_le_succ hk)
          ((ContinuousMap.IccExtend hsumT (glueXTs hk ht0 hτ u v hmatch)) (s + t0)) =
          NSN (three_le_succ hk) ((ContinuousMap.IccExtend hτ v) s) :=
      fun s hs => by
        have : t0 ≤ s + t0 := le_add_of_nonneg_left hs.1
        have hs' : s + t0 ∈ Icc 0 (t0 + τ) := shift_time_mem ht0 (by linarith) hs
        rw [IccExtend_glue_gt hk ht0 hτ u v hmatch this hs', add_sub_cancel_right]
    -- finish by rewriting both Duhamel terms
    rw [hheat]
    simp only [map_sub]
    have hco := (duhHigh_congr hk hν ht0 hsrc0)
    have hcs := (duhHigh_congr hk hν hσ hsrcσ)
    have : duhHigh hk ν
        (fun s => NSN (three_le_succ hk)
          ((ContinuousMap.IccExtend hsumT (glueXTs hk ht0 hτ u v hmatch)) s)) (t : ℝ) =
        heatH (k + 1) (ν * ((t : ℝ) - t0))
          (duhHigh hk ν (fun s => NSN (three_le_succ hk)
            ((ContinuousMap.IccExtend ht0 u) s)) t0) +
          duhHigh hk ν (fun s => NSN (three_le_succ hk)
            ((ContinuousMap.IccExtend hτ v) s)) ((t : ℝ) - t0) := by
      rw [← htval, hsplit, hco, hcs]
      simp [add_sub_cancel]
    rw [this]
    abel

#print axioms PersistenceHm.isMildS_glue


lemma two_mul_le_two_pow_succ (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    2 * x ≤ (2 : ℝ) ^ (n + 1) * x := by
  have : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  calc 2 * x = (1 : ℝ) * (2 * x) := (one_mul _).symm
    _ ≤ (2 : ℝ) ^ n * (2 * x) :=
      mul_le_mul_of_nonneg_right this (mul_nonneg (by norm_num) hx)
    _ = (2 : ℝ) ^ (n + 1) * x := by rw [pow_succ]; ring

lemma persist_chunk_bound (hk : 2 ≤ k) {ν T R3 : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (hR3 : 0 ≤ R3) (u₀ : Hm (k + 1)) {u : XTs k T}
    (hu : IsMildS hk hT ν u₀ u)
    (hbd3 : ∀ t : Icc 0 T, ‖incl (three_le_succ hk) (u t)‖ ≤ R3)
    (n : ℕ) (hle : T ≤ (n : ℝ) * timePersist k ν R3) :
    ‖u‖ ≤ (2 : ℝ) ^ n * ‖u₀‖ := by
  induction n generalizing T u u₀ with
  | zero =>
    have hT0 : T = 0 := le_antisymm (by simpa using hle) hT
    refine (ContinuousMap.norm_le u (mul_nonneg (by norm_num) (norm_nonneg u₀))).2
      fun t => ?_
    have ht0 : (t : ℝ) = 0 := le_antisymm (hT0 ▸ t.2.2) t.2.1
    have hu0 := hu t
    simp only [ht0, mul_zero, heatH_zero, duhHigh_zero hk, sub_zero] at hu0
    rw [hu0]; simp
  | succ n ih =>
    by_cases hTP : T ≤ timePersist k ν R3
    · have hdoub := apriori_double hk hν hT hR3
        (visc_le_of_le_timePersist hν k hT hTP) u₀ hu hbd3
      exact hdoub.trans (two_mul_le_two_pow_succ n ‖u₀‖ (norm_nonneg _))
    · set t0 := timePersist k ν R3
      have ht0pos : 0 ≤ t0 := timePersist_nonneg hν k R3
      have hlt : t0 < T := not_le.mp hTP
      have hτ : 0 ≤ T - t0 := sub_nonneg.2 hlt.le
      have hsum : t0 + (T - t0) = T := add_sub_cancel t0 T
      have huR := isMildS_restrict hk hν hT ht0pos hlt.le u₀ hu
      have hbdR : ∀ s : Icc 0 t0,
          ‖incl (three_le_succ hk) (restrictXTs hk hlt.le u s)‖ ≤ R3 := fun s =>
        hbd3 ⟨s.1, ⟨s.2.1, s.2.2.trans hlt.le⟩⟩
      have hboundR := apriori_double hk hν ht0pos hR3 (timePersist_visc hν k R3)
        u₀ huR hbdR
      have huS := isMildS_shift hk hν hT ht0pos hτ hsum.le u₀ hu
      have hleS : T - t0 ≤ (n : ℝ) * t0 := by
        have : T ≤ (n : ℝ) * t0 + t0 := by
          simpa [Nat.cast_succ, add_mul, one_mul] using hle
        linarith
      have hbdS : ∀ σ : Icc 0 (T - t0),
          ‖incl (three_le_succ hk) (shiftXTs hk ht0pos hτ hsum.le u σ)‖ ≤ R3 :=
        fun σ => by
          have hmem := shift_time_mem ht0pos hsum.le σ.2
          change ‖incl (three_le_succ hk) (u ⟨σ.1 + t0, hmem⟩)‖ ≤ R3
          exact hbd3 _
      have hboundS := ih (T := T - t0) hτ (u ⟨t0, ⟨ht0pos, hlt.le⟩⟩) huS hbdS hleS
      have hpow : (2 : ℝ) * ‖u₀‖ ≤ (2 : ℝ) ^ (n + 1) * ‖u₀‖ :=
        two_mul_le_two_pow_succ n ‖u₀‖ (norm_nonneg _)
      have hpt : ∀ t : Icc 0 T, ‖u t‖ ≤ (2 : ℝ) ^ (n + 1) * ‖u₀‖ := fun t => by
        rcases le_or_gt (t : ℝ) t0 with ht | ht
        · have heq : restrictXTs hk hlt.le u ⟨t.1, ⟨t.2.1, ht⟩⟩ = u t := rfl
          rw [← heq]
          exact ((norm_coe_le_norm _ _).trans hboundR).trans hpow
        · have hσ : (t : ℝ) - t0 ∈ Icc 0 (T - t0) :=
            ⟨sub_nonneg.2 ht.le, by linarith [t.2.2]⟩
          have heq : shiftXTs hk ht0pos hτ hsum.le u ⟨_, hσ⟩ = u t := by
            apply congrArg (fun x : Icc 0 T => u x)
            ext
            simp
          rw [← heq]
          have h1 : ‖shiftXTs hk ht0pos hτ hsum.le u ⟨_, hσ⟩‖ ≤
              (2 : ℝ) ^ n * ‖u ⟨t0, ⟨ht0pos, hlt.le⟩⟩‖ :=
            (norm_coe_le_norm _ _).trans hboundS
          have hu0le : ‖u ⟨t0, ⟨ht0pos, hlt.le⟩⟩‖ ≤ 2 * ‖u₀‖ := by
            have heqR : restrictXTs hk hlt.le u ⟨t0, ⟨ht0pos, le_rfl⟩⟩ =
                u ⟨t0, ⟨ht0pos, hlt.le⟩⟩ := rfl
            rw [← heqR]
            exact (norm_coe_le_norm _ _).trans hboundR
          have h2 : (2 : ℝ) ^ n * ‖u ⟨t0, ⟨ht0pos, hlt.le⟩⟩‖ ≤
              (2 : ℝ) ^ (n + 1) * ‖u₀‖ := by
            calc (2 : ℝ) ^ n * ‖u ⟨t0, ⟨ht0pos, hlt.le⟩⟩‖
                ≤ (2 : ℝ) ^ n * (2 * ‖u₀‖) :=
                  mul_le_mul_of_nonneg_left hu0le (pow_nonneg (by norm_num) n)
              _ = (2 : ℝ) ^ (n + 1) * ‖u₀‖ := by ring
          exact h1.trans h2
      exact (ContinuousMap.norm_le u
          (mul_nonneg (pow_nonneg (by norm_num) _) (norm_nonneg u₀))).2 hpt

#print axioms PersistenceHm.persist_chunk_bound


/-! ## Restriction and shift of Ĥ³ mild paths -/

def restrictXT {T T' : ℝ} (h : T' ≤ T) (u : XT T) : XT T' :=
  ContinuousMap.mk
    (fun t => u ⟨t.1, ⟨t.2.1, le_trans t.2.2 h⟩⟩)
    (u.continuous.comp
      (Continuous.subtype_mk continuous_subtype_val fun t => ⟨t.2.1, t.2.2.trans h⟩))

lemma IccExtend_restrictXT {T T' : ℝ} (hT : 0 ≤ T) (hT' : 0 ≤ T') (h : T' ≤ T)
    (u : XT T) {s : ℝ} (hs : s ∈ Icc 0 T') :
    ContinuousMap.IccExtend hT' (restrictXT h u) s =
      ContinuousMap.IccExtend hT u s := by
  rw [ContinuousMap.coe_IccExtend, ContinuousMap.coe_IccExtend,
    Set.IccExtend_of_mem (hx := hs),
    Set.IccExtend_of_mem (hx := ⟨hs.1, hs.2.trans h⟩)]
  rfl

lemma isMild_restrict {ν T T' : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hT' : 0 ≤ T')
    (h : T' ≤ T) (u₀ : Hm 3) {u : XT T} (hu : IsMild hT ν u₀ u) :
    IsMild hT' ν u₀ (restrictXT h u) := by
  intro t
  have htT : (t : ℝ) ≤ T := t.2.2.trans h
  have huv := hu ⟨t.1, ⟨t.2.1, htT⟩⟩
  have hpt : restrictXT h u t = u ⟨t.1, ⟨t.2.1, htT⟩⟩ := rfl
  rw [hpt, huv]
  have hsrc : ∀ s ∈ Icc 0 (t : ℝ),
      Nonlinear.NSN ((ContinuousMap.IccExtend hT u) s) =
        Nonlinear.NSN ((ContinuousMap.IccExtend hT' (restrictXT h u)) s) := fun s hs => by
    have hs' : s ∈ Icc 0 T' := ⟨hs.1, hs.2.trans t.2.2⟩
    rw [IccExtend_restrictXT hT hT' h u hs']
  rw [duhν_congr hν t.2.1 hsrc]

def shiftXT {T t0 τ : ℝ} (ht0 : 0 ≤ t0) (hτ : 0 ≤ τ) (hsum : t0 + τ ≤ T)
    (u : XT T) : XT τ :=
  ContinuousMap.mk
    (fun σ => u ⟨σ.1 + t0, shift_time_mem ht0 hsum σ.2⟩)
    (u.continuous.comp
      (Continuous.subtype_mk
        (continuous_subtype_val.add
          (continuous_const : Continuous (fun _ : Icc (0 : ℝ) τ => t0)))
        fun σ => shift_time_mem ht0 hsum σ.2))

lemma IccExtend_shiftXT {T t0 τ : ℝ} (hT : 0 ≤ T) (ht0 : 0 ≤ t0) (hτ : 0 ≤ τ)
    (hsum : t0 + τ ≤ T) (u : XT T) {s : ℝ} (hs : s ∈ Icc 0 τ) :
    ContinuousMap.IccExtend hτ (shiftXT ht0 hτ hsum u) s =
      ContinuousMap.IccExtend hT u (s + t0) := by
  have hsT : s + t0 ∈ Icc 0 T := shift_time_mem ht0 hsum hs
  rw [ContinuousMap.coe_IccExtend, ContinuousMap.coe_IccExtend,
    Set.IccExtend_of_mem (hx := hs), Set.IccExtend_of_mem (hx := hsT)]
  apply congrArg u
  ext
  rfl

lemma isMild_shift {ν T t0 τ : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (ht0 : 0 ≤ t0) (hτ : 0 ≤ τ) (hsum : t0 + τ ≤ T)
    (u₀ : Hm 3) {u : XT T} (hu : IsMild hT ν u₀ u) :
    IsMild hτ ν (u ⟨t0, ⟨ht0, le_trans (le_add_of_nonneg_right hτ) hsum⟩⟩)
      (shiftXT ht0 hτ hsum u) := by
  intro σ
  have hpt : ((σ : ℝ) + t0) ∈ Icc 0 T := shift_time_mem ht0 hsum σ.2
  have huσ := hu ⟨(σ : ℝ) + t0, hpt⟩
  have hu0 := hu ⟨t0, ⟨ht0, le_trans (le_add_of_nonneg_right hτ) hsum⟩⟩
  have hsh : shiftXT ht0 hτ hsum u σ = u ⟨(σ : ℝ) + t0, hpt⟩ := by
    apply congrArg u
    ext
    rfl
  rw [hsh, huσ]
  have hN : Continuous (fun s => Nonlinear.NSN ((ContinuousMap.IccExtend hT u) s)) :=
    continuous_NSN_extU hT u
  have htime : (σ : ℝ) + t0 = t0 + (σ : ℝ) := add_comm _ _
  simp only [htime]
  rw [duhν_cocycle (m := 2) hν hN ht0 σ.2.1]
  have hheat : heatH 3 (ν * (t0 + (σ : ℝ))) u₀ =
      heatH 3 (ν * (σ : ℝ)) (heatH 3 (ν * t0) u₀) := by
    rw [mul_add, add_comm (ν * t0)]
    exact (heatH_heatH (mul_nonneg hν.le σ.2.1) (mul_nonneg hν.le ht0) u₀).symm
  rw [hheat, hu0, map_sub]
  have hsrc : ∀ s ∈ Icc 0 (σ : ℝ),
      Nonlinear.NSN ((ContinuousMap.IccExtend hT u) (s + t0)) =
        Nonlinear.NSN ((ContinuousMap.IccExtend hτ (shiftXT ht0 hτ hsum u)) s) := fun s hs => by
    have hsτ : s ∈ Icc 0 τ := ⟨hs.1, hs.2.trans σ.2.2⟩
    rw [IccExtend_shiftXT hT ht0 hτ hsum u hsτ]
  rw [duhν_congr hν σ.2.1 hsrc]
  abel

#print axioms PersistenceHm.isMild_restrict
#print axioms PersistenceHm.isMild_shift


/-! ## Persistence of Ĥ^{k+1} on the Ĥ³ local existence time -/

lemma localTimeS_ge_of_norm_le {ν : ℝ} (hν : 0 < ν) {w : Hm (k + 1)} {R : ℝ}
    (hR : 0 ≤ R) (hw : ‖w‖ ≤ R) :
    timeSlot ν (1 / (2 * (36 * Cm (k + 1) * (2 * R + 1) + 1))) ≤ localTimeS ν w := by
  unfold localTimeS deltaS radS
  have hdenR : 0 < 2 * (36 * Cm (k + 1) * (2 * R + 1) + 1) :=
    mul_pos (by norm_num)
      (add_pos_of_nonneg_of_pos (mul_nonneg (Cm36_nonneg k) (by linarith)) one_pos)
  have hδ :
      1 / (2 * (36 * Cm (k + 1) * (2 * R + 1) + 1)) ≤
        1 / (2 * (36 * Cm (k + 1) * (2 * ‖w‖ + 1) + 1)) := by
    refine one_div_le_one_div_of_le (denS_pos w) ?_
    have : 36 * Cm (k + 1) * (2 * ‖w‖ + 1) ≤ 36 * Cm (k + 1) * (2 * R + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [norm_nonneg w]) (Cm36_nonneg k)
    linarith
  exact timeSlot_mono hν.le (one_div_pos.2 hdenR).le hδ

lemma localTime_ge_of_norm_le {ν : ℝ} (hν : 0 < ν) {w : Hm 3} {R : ℝ}
    (hR : 0 ≤ R) (hw : ‖w‖ ≤ R) :
    timeSlot ν (1 / (2 * (18 * Cstar * (2 * R + 1) + 1))) ≤ localTime ν w := by
  unfold localTime delta rad
  have hdenR : 0 < 2 * (18 * Cstar * (2 * R + 1) + 1) :=
    mul_pos (by norm_num)
      (add_pos_of_nonneg_of_pos
        (mul_nonneg (mul_nonneg (by norm_num) Cstar_nonneg) (by linarith)) one_pos)
  have hδ :
      1 / (2 * (18 * Cstar * (2 * R + 1) + 1)) ≤
        1 / (2 * (18 * Cstar * (2 * ‖w‖ + 1) + 1)) := by
    refine one_div_le_one_div_of_le (den_pos w) ?_
    have : 18 * Cstar * (2 * ‖w‖ + 1) ≤ 18 * Cstar * (2 * R + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [norm_nonneg w])
        (mul_nonneg (by norm_num) Cstar_nonneg)
    linarith
  exact timeSlot_mono hν.le (one_div_pos.2 hdenR).le hδ

lemma isMildS_zero' (hk : 2 ≤ k) {ν T : ℝ} (hT : 0 ≤ T) (u₀ : Hm (k + 1))
    {u : XTs k T} (hu : IsMildS hk hT ν u₀ u) :
    u ⟨0, ⟨le_rfl, hT⟩⟩ = u₀ := by
  have h := hu ⟨0, ⟨le_rfl, hT⟩⟩
  simpa [heatH_zero, duhHigh_zero hk, sub_zero] using h

lemma inclMap_restrict (hk : 2 ≤ k) {T T' : ℝ} (h : T' ≤ T) (u : XTs k T) :
    inclMap hk (restrictXTs hk h u) = restrictXT h (inclMap hk u) :=
  rfl

lemma inclMap_shift (hk : 2 ≤ k) {T t0 τ : ℝ} (ht0 : 0 ≤ t0) (hτ : 0 ≤ τ)
    (hsum : t0 + τ ≤ T) (u : XTs k T) :
    inclMap hk (shiftXTs hk ht0 hτ hsum u) = shiftXT ht0 hτ hsum (inclMap hk u) := by
  refine ContinuousMap.ext fun σ => ?_
  simp [inclMap, shiftXTs, shiftXT]

lemma inclMap_mem_ball (hk : 2 ≤ k) {T R : ℝ} (hR : 0 ≤ R) {u : XTs k T}
    (h : ∀ t : Icc 0 T, ‖incl (three_le_succ hk) (u t)‖ ≤ R) :
    inclMap hk u ∈ closedBall (0 : XT T) R := by
  rw [mem_closedBall_iff_norm, sub_zero]
  exact (ContinuousMap.norm_le _ hR).2 fun t => by
    change ‖incl (three_le_succ hk) (u t)‖ ≤ R
    exact h t

lemma restrictXT_mem_ball {T T' R : ℝ} (h : T' ≤ T) {u : XT T}
    (hu : u ∈ closedBall (0 : XT T) R) :
    restrictXT h u ∈ closedBall (0 : XT T') R := by
  rw [mem_closedBall_iff_norm, sub_zero] at hu ⊢
  refine (ContinuousMap.norm_le _ (le_trans (norm_nonneg u) hu)).2 fun t => ?_
  have : restrictXT h u t = u ⟨t.1, ⟨t.2.1, t.2.2.trans h⟩⟩ := rfl
  rw [this]
  exact (norm_coe_le_norm u _).trans hu

structure PersistData (hk : 2 ≤ k) (ν : ℝ) (u₀ : Hm (k + 1)) (t : ℝ) where
  nonneg : 0 ≤ t
  le_T3 : t ≤ localTime ν (incl (three_le_succ hk) u₀)
  path : XTs k t
  mild : IsMildS hk nonneg ν u₀ path
  inclBound : ∀ s : Icc 0 t,
    ‖incl (three_le_succ hk) (path s)‖ ≤ rad (incl (three_le_succ hk) u₀)

def persistSet (hk : 2 ≤ k) (ν : ℝ) (u₀ : Hm (k + 1)) : Set ℝ :=
  { t | Nonempty (PersistData hk ν u₀ t) }

lemma persistSet_nonempty (hk : 2 ≤ k) {ν : ℝ} (hν : 0 < ν) (u₀ : Hm (k + 1)) :
    (persistSet hk ν u₀).Nonempty := by
  obtain ⟨hTpos, u, -, huM, hball, -⟩ := persist_on_minTime hk hν u₀
  refine ⟨_, ⟨PersistData.mk
      (le_min (localTimeS_nonneg hν u₀)
        (localTime_nonneg hν (incl (three_le_succ hk) u₀)))
      (min_le_right _ _) u huM (fun s =>
        (norm_coe_le_norm (inclMap hk u) s).trans (by
          rw [mem_closedBall_iff_norm, sub_zero] at hball
          exact hball))⟩⟩

lemma persistSet_anti (hk : 2 ≤ k) {ν : ℝ} (hν : 0 < ν) (u₀ : Hm (k + 1))
    {t t' : ℝ} (ht : t ∈ persistSet hk ν u₀) (ht' : 0 ≤ t') (hle : t' ≤ t) :
    t' ∈ persistSet hk ν u₀ := by
  obtain ⟨W⟩ := ht
  refine ⟨PersistData.mk ht' (hle.trans W.le_T3)
      (restrictXTs hk hle W.path)
      (isMildS_restrict hk hν W.nonneg ht' hle u₀ W.mild)
      (fun s => by
        change ‖incl (three_le_succ hk)
            (W.path ⟨s.1, ⟨s.2.1, s.2.2.trans hle⟩⟩)‖ ≤ _
        exact W.inclBound _)⟩

lemma persistSet_bddAbove (hk : 2 ≤ k) (ν : ℝ) (u₀ : Hm (k + 1)) :
    BddAbove (persistSet hk ν u₀) :=
  ⟨localTime ν (incl (three_le_succ hk) u₀), fun _ ht => ht.some.le_T3⟩

#print axioms PersistenceHm.persistSet_nonempty


lemma add_le_of_eq_left {s t r c : ℝ} (h : s = t) (hle : c ≤ s + r) :
    c ≤ t + r :=
  h ▸ hle

lemma one_add_norm_le_rad (w : Hm 3) : ‖w‖ + 1 ≤ rad w := by
  unfold rad
  linarith [norm_nonneg w]

/-- `Lp` defines `dist a b` as `‖-a + b‖` (definitionally). -/
lemma dist_lt_one_iff_neg_add {a b : Hm 3} (h : dist a b < 1) :
    ‖-a + b‖ < 1 := h

lemma eq_imp_one_add_norm_le_rad {x w : Hm 3} (h : x = w) :
    ‖x‖ + 1 ≤ rad w := by
  cases h
  exact one_add_norm_le_rad _

lemma norm_le_of_eq_add {x y z : Hm 3} (h : x = y + z) :
    ‖x‖ ≤ ‖y‖ + ‖z‖ := by
  have hadd : ‖y + z‖ ≤ ‖y‖ + ‖z‖ := norm_add_le y z
  cases h
  exact hadd

lemma neg_neg_add_add (a b : Hm 3) : -(-a + b) + b = a := by
  rw [neg_add, neg_neg, add_assoc, neg_add_cancel, add_zero]

lemma norm_neg_neg_add (a b : Hm 3) : ‖-(-a + b)‖ = ‖-a + b‖ :=
  norm_neg _

lemma norm_le_neg_neg_add (a b : Hm 3) :
    ‖a‖ ≤ ‖-(-a + b)‖ + ‖b‖ :=
  norm_le_of_eq_add (neg_neg_add_add a b).symm

lemma norm_le_neg_add (a b : Hm 3) : ‖a‖ ≤ ‖-a + b‖ + ‖b‖ :=
  add_le_of_eq_left (norm_neg_neg_add a b) (norm_le_neg_neg_add a b)

lemma neg_add_lt_one_norm_le {a b : Hm 3} (h : ‖-a + b‖ < 1) :
    ‖a‖ ≤ ‖b‖ + 1 := by
  have h1 := norm_le_neg_add a b
  linarith

lemma neg_add_lt_one_eq_le_rad {a b w : Hm 3} (heq : b = w) (h : ‖-a + b‖ < 1) :
    ‖a‖ ≤ rad w :=
  (neg_add_lt_one_norm_le h).trans (eq_imp_one_add_norm_le_rad heq)

lemma eq_imp_norm_le {x y : Hm 3} {R : ℝ} (h : x = y) (hle : ‖y‖ ≤ R) :
    ‖x‖ ≤ R := by
  cases h
  exact hle

lemma shiftXT_mem_rad {T t0 τ η : ℝ} (ht0 : 0 ≤ t0) (hτ : 0 ≤ τ)
    (hsum : t0 + τ ≤ T) (u : XT T) {w : Hm 3}
    (hw : u ⟨t0, ⟨ht0, (le_add_of_nonneg_right hτ).trans hsum⟩⟩ = w)
    (ηpos : 0 < η) (hle : τ ≤ η / 2)
    (hη : ∀ x y : Icc (0 : ℝ) T, dist x y < η → dist (u x) (u y) < 1) :
    shiftXT ht0 hτ hsum u ∈ closedBall (0 : XT τ) (rad w) := by
  rw [mem_closedBall_iff_norm, sub_zero]
  refine (ContinuousMap.norm_le _ (rad_nonneg _)).2 fun σ => ?_
  have hpt : ((σ : ℝ) + t0) ∈ Icc 0 T := shift_time_mem ht0 hsum σ.2
  have hdist : dist (⟨σ.1 + t0, hpt⟩ : Icc 0 T)
      (⟨t0, ⟨ht0, (le_add_of_nonneg_right hτ).trans hsum⟩⟩ : Icc 0 T) < η := by
    rw [Subtype.dist_eq, Real.dist_eq, add_sub_cancel_right, abs_of_nonneg σ.2.1]
    exact (σ.2.2.trans hle).trans_lt (half_lt_self ηpos)
  exact eq_imp_norm_le
    (show shiftXT ht0 hτ hsum u σ = u ⟨σ.1 + t0, hpt⟩ by
      apply congrArg u; ext; rfl)
    (neg_add_lt_one_eq_le_rad hw (dist_lt_one_iff_neg_add (hη _ _ hdist)))

lemma persist_path_norm_le (hk : 2 ≤ k) {ν : ℝ} (hν : 0 < ν) (u₀ : Hm (k + 1))
    {t : ℝ} (W : PersistData hk ν u₀ t) {N : ℕ}
    {R3 : ℝ} (hR3 : 0 ≤ R3)
    (hR3def : R3 = rad (incl (three_le_succ hk) u₀))
    (hNcov : localTime ν (incl (three_le_succ hk) u₀) ≤
      (N : ℝ) * timePersist k ν R3) :
    ‖W.path‖ ≤ (2 : ℝ) ^ N * ‖u₀‖ := by
  subst hR3def
  exact persist_chunk_bound hk hν W.nonneg (rad_nonneg _) u₀ W.mild W.inclBound N
    (W.le_T3.trans hNcov)

lemma persist_restart_window (hk : 2 ≤ k) {ν : ℝ} (hν : 0 < ν) (u₀ : Hm (k + 1)) :
    ∃ δstar, 0 < δstar ∧
      ∀ {t : ℝ} (W : PersistData hk ν u₀ t),
        ∃ τ, min δstar
            (localTime ν (incl (three_le_succ hk) u₀) - t) ≤ τ ∧
          0 ≤ τ ∧ t + τ ∈ persistSet hk ν u₀ := by
  set T3 := localTime ν (incl (three_le_succ hk) u₀)
  have hT3 : 0 ≤ T3 := localTime_nonneg hν _
  set R3 := rad (incl (three_le_succ hk) u₀)
  have hR3 : 0 ≤ R3 := rad_nonneg _
  have hδpos : 0 < timePersist k ν R3 := timePersist_pos hν k R3
  obtain ⟨N, hN⟩ := exists_nat_ge (T3 / timePersist k ν R3)
  have hNcov : T3 ≤ (N : ℝ) * timePersist k ν R3 := (div_le_iff₀ hδpos).1 hN
  set B := (2 : ℝ) ^ N * ‖u₀‖
  have hB : 0 ≤ B := mul_nonneg (pow_nonneg (by norm_num) _) (norm_nonneg _)
  obtain ⟨_, u3, hu3mem, hu3M, _⟩ :=
    local_mild_existence ν hν (incl (three_le_succ hk) u₀)
  have huc : UniformContinuous (fun x : Icc (0 : ℝ) T3 => u3 x) :=
    CompactSpace.uniformContinuous_of_continuous u3.continuous
  obtain ⟨η, ηpos, hη⟩ :
      ∃ η > (0 : ℝ), ∀ x y : Icc (0 : ℝ) T3, dist x y < η → dist (u3 x) (u3 y) < 1 := by
    have := (Metric.uniformContinuous_iff.1 huc) (1 : ℝ) (by norm_num)
    exact this
  set δS := timeSlot ν (1 / (2 * (36 * Cm (k + 1) * (2 * B + 1) + 1)))
  set δ3 := timeSlot ν (1 / (2 * (18 * Cstar * (2 * R3 + 1) + 1)))
  set δstar := min (min δS δ3) (η / 2)
  have hδSpos : 0 < δS :=
    timeSlot_pos hν (one_div_pos.2 (mul_pos (by norm_num)
      (add_pos_of_nonneg_of_pos
        (mul_nonneg (Cm36_nonneg k) (by linarith [hB])) one_pos)))
  have hδ3pos : 0 < δ3 :=
    timeSlot_pos hν (one_div_pos.2 (mul_pos (by norm_num)
      (add_pos_of_nonneg_of_pos
        (mul_nonneg (mul_nonneg (by norm_num) Cstar_nonneg)
          (by linarith [hR3])) one_pos)))
  have hδstar_pos : 0 < δstar := lt_min (lt_min hδSpos hδ3pos) (half_pos ηpos)
  refine ⟨δstar, hδstar_pos, ?_⟩
  intro t W
  have hnormW : ‖W.path‖ ≤ B :=
    persist_chunk_bound hk hν W.nonneg hR3 u₀ W.mild W.inclBound N
      (W.le_T3.trans hNcov)
  set w0 := W.path ⟨t, ⟨W.nonneg, le_rfl⟩⟩
  have hw0B : ‖w0‖ ≤ B := (norm_coe_le_norm _ _).trans hnormW
  have hlocS : δS ≤ localTimeS ν w0 := localTimeS_ge_of_norm_le hν hB hw0B
  have hincl0 : ‖incl (three_le_succ hk) w0‖ ≤ R3 :=
    W.inclBound ⟨t, ⟨W.nonneg, le_rfl⟩⟩
  have hloc3 : δ3 ≤ localTime ν (incl (three_le_succ hk) w0) :=
    localTime_ge_of_norm_le hν hR3 hincl0
  set Tmin' := min (localTimeS ν w0) (localTime ν (incl (three_le_succ hk) w0))
  have hTmin'_nonneg : 0 ≤ Tmin' :=
    le_min (localTimeS_nonneg hν w0)
      (localTime_nonneg hν (incl (three_le_succ hk) w0))
  obtain ⟨_, vS, _, hvM, hvball, _⟩ := persist_on_minTime hk hν w0
  have hTmin'_ge : min δS δ3 ≤ Tmin' := min_le_min hlocS hloc3
  have hTmin'_δstar : δstar ≤ Tmin' := (min_le_left _ _).trans hTmin'_ge
  have hτ0gap : 0 ≤ T3 - t := sub_nonneg.2 W.le_T3
  have hτη : 0 ≤ η / 2 := (half_pos ηpos).le
  set τ := min Tmin' (min (T3 - t) (η / 2))
  have hτ : 0 ≤ τ := le_min (le_trans hδstar_pos.le hTmin'_δstar) (le_min hτ0gap hτη)
  have hτ_le_Tmin' : τ ≤ Tmin' := min_le_left _ _
  have hτ_le_gap : τ ≤ T3 - t := (min_le_right _ _).trans (min_le_left _ _)
  have hτ_le_η : τ ≤ η / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hsum : t + τ ≤ T3 := by linarith [hτ_le_gap]
  have hvMτ : IsMildS hk hτ ν w0 (restrictXTs hk hτ_le_Tmin' vS) :=
    isMildS_restrict hk hν hTmin'_nonneg hτ hτ_le_Tmin' w0 hvM
  have hmatch : restrictXTs hk hτ_le_Tmin' vS ⟨0, ⟨le_rfl, hτ⟩⟩ =
      W.path ⟨t, ⟨W.nonneg, le_rfl⟩⟩ :=
    isMildS_zero' hk hTmin'_nonneg w0 hvM
  set g := glueXTs hk W.nonneg hτ W.path (restrictXTs hk hτ_le_Tmin' vS) hmatch
  have hgM : IsMildS hk (add_nonneg W.nonneg hτ) ν u₀ g :=
    isMildS_glue hk hν W.nonneg hτ u₀ hmatch W.mild hvMτ
  have hident0 : inclMap hk W.path = restrictXT W.le_T3 u3 :=
    unique_mild_in_ball hν W.nonneg (incl (three_le_succ hk) u₀)
      (visc_le_of_le_localTime hν _ W.nonneg W.le_T3)
      (inclMap_mem_ball hk hR3 W.inclBound)
      (restrictXT_mem_ball W.le_T3 hu3mem)
      (isMild_inclMap hk hν W.nonneg u₀ W.mild)
      (isMild_restrict hν hT3 W.nonneg W.le_T3 _ hu3M)
  have hw0u3 : incl (three_le_succ hk) w0 =
      u3 ⟨t, ⟨W.nonneg, W.le_T3⟩⟩ := by
    have := congrArg (fun u : XT t => u ⟨t, ⟨W.nonneg, le_rfl⟩⟩) hident0
    simpa [inclMap, restrictXT] using this
  have hwpt : u3 ⟨t, ⟨W.nonneg, (le_add_of_nonneg_right hτ).trans hsum⟩⟩ =
      incl (three_le_succ hk) w0 := by
    trans u3 ⟨t, ⟨W.nonneg, W.le_T3⟩⟩
    · apply congrArg u3; ext; rfl
    · exact hw0u3.symm
  have hshift_mem :
      shiftXT W.nonneg hτ hsum u3 ∈
        closedBall (0 : XT τ) (rad (incl (three_le_succ hk) w0)) :=
    shiftXT_mem_rad W.nonneg hτ hsum u3 hwpt ηpos hτ_le_η hη
  have hidentσ : inclMap hk (restrictXTs hk hτ_le_Tmin' vS) =
      shiftXT W.nonneg hτ hsum u3 :=
    unique_mild_in_ball hν hτ (incl (three_le_succ hk) w0)
      (visc_le_of_le_localTime hν _ hτ
        (hτ_le_Tmin'.trans (min_le_right _ _)))
      (by
        rw [inclMap_restrict]
        exact restrictXT_mem_ball hτ_le_Tmin' hvball)
      hshift_mem
      (isMild_inclMap hk hν hτ w0 hvMτ)
      (by
        have hsh := isMild_shift hν hT3 W.nonneg hτ hsum
          (incl (three_le_succ hk) u₀) hu3M
        exact hwpt ▸ hsh)
  have hgB : ∀ s : Icc 0 (t + τ),
      ‖incl (three_le_succ hk) (g s)‖ ≤ R3 := fun s => by
    rcases le_or_gt (s : ℝ) t with hs | hs
    · have := glue_eval_le hk W.nonneg hτ W.path
        (restrictXTs hk hτ_le_Tmin' vS) hmatch s hs
      rw [this]
      exact W.inclBound ⟨s.1, ⟨s.2.1, hs⟩⟩
    · have hgt := glue_eval_gt hk W.nonneg hτ W.path
        (restrictXTs hk hτ_le_Tmin' vS) hmatch s hs
      rw [hgt]
      have hσ : (s : ℝ) - t ∈ Icc 0 τ :=
        ⟨sub_nonneg.2 hs.le, by linarith [s.2.2]⟩
      have hinc : incl (three_le_succ hk)
          (restrictXTs hk hτ_le_Tmin' vS ⟨s.1 - t, hσ⟩) =
          u3 ⟨s.1, ⟨s.2.1, s.2.2.trans hsum⟩⟩ := by
        have hpt := congrArg (fun u : XT τ => u ⟨s.1 - t, hσ⟩) hidentσ
        have hshift :
            shiftXT W.nonneg hτ hsum u3 ⟨s.1 - t, hσ⟩ =
              u3 ⟨s.1, ⟨s.2.1, s.2.2.trans hsum⟩⟩ := by
          apply congrArg u3
          ext
          exact sub_add_cancel s.1 t
        simpa [inclMap] using hpt.trans hshift
      rw [hinc]
      exact (norm_coe_le_norm u3 _).trans (by
        have := mem_closedBall_iff_norm.mp hu3mem
        rwa [sub_zero] at this)
  refine ⟨τ, ?_, hτ, persistSet_anti hk hν u₀
      ⟨PersistData.mk (add_nonneg W.nonneg hτ) hsum g hgM hgB⟩
      (add_nonneg W.nonneg hτ) le_rfl⟩
  -- min δstar (T3 - t) ≤ τ
  have hswap : min δstar (T3 - t) = min (min δS δ3) (min (T3 - t) (η / 2)) := by
    calc
      min δstar (T3 - t)
          = min (min (min δS δ3) (η / 2)) (T3 - t) := rfl
      _ = min (min δS δ3) (min (η / 2) (T3 - t)) := min_assoc _ _ _
      _ = min (min δS δ3) (min (T3 - t) (η / 2)) := by rw [min_comm (η / 2)]
  rw [hswap]
  exact min_le_min hTmin'_ge le_rfl

lemma Tstar_mem (hk : 2 ≤ k) {ν : ℝ} (hν : 0 < ν) (u₀ : Hm (k + 1)) :
    sSup (persistSet hk ν u₀) ∈ persistSet hk ν u₀ := by
  set T3 := localTime ν (incl (three_le_succ hk) u₀)
  set S := persistSet hk ν u₀
  have hSne : S.Nonempty := persistSet_nonempty hk hν u₀
  have hSbd : BddAbove S := persistSet_bddAbove hk ν u₀
  set Tstar := sSup S
  have hTstar_le : Tstar ≤ T3 := csSup_le hSne fun t ht => ht.some.le_T3
  obtain ⟨δstar, hδstar_pos, hrest⟩ := persist_restart_window hk hν u₀
  obtain ⟨t, htS, htclose⟩ : ∃ t ∈ S, Tstar - δstar < t :=
    exists_lt_of_lt_csSup hSne (sub_lt_self Tstar hδstar_pos)
  have ht_le : t ≤ Tstar := le_csSup hSbd htS
  rcases eq_or_lt_of_le ht_le with htEq | _htlt
  · rwa [← htEq]
  obtain ⟨W⟩ := htS
  obtain ⟨τ, hτge, hτ0, hτmem⟩ := hrest W
  have hgap : Tstar - t ≤ τ := by
    have hA : Tstar - t < δstar := by linarith [htclose]
    have hB : Tstar - t ≤ T3 - t := sub_le_sub_right hTstar_le t
    exact (le_min hA.le hB).trans hτge
  exact persistSet_anti hk hν u₀ hτmem (le_trans W.nonneg ht_le)
    (by linarith [hgap])

/-- The Ĥ^{k+1} mild solution persists on the full Ĥ³ local existence interval. -/
theorem persist_on_H3_time (hk : 2 ≤ k) {ν : ℝ} (hν : 0 < ν) (u₀ : Hm (k + 1)) :
    let T := localTime ν (incl (three_le_succ hk) u₀)
    ∃ u : XTs k T,
      IsMildS hk (localTime_nonneg hν (incl (three_le_succ hk) u₀)) ν u₀ u ∧
      IsMild (localTime_nonneg hν (incl (three_le_succ hk) u₀)) ν
        (incl (three_le_succ hk) u₀) (inclMap hk u) ∧
      inclMap hk u ∈
        closedBall (0 : XT T) (rad (incl (three_le_succ hk) u₀)) := by
  have hSne : (persistSet hk ν u₀).Nonempty := persistSet_nonempty hk hν u₀
  have hSbd : BddAbove (persistSet hk ν u₀) := persistSet_bddAbove hk ν u₀
  have hmem : sSup (persistSet hk ν u₀) ∈ persistSet hk ν u₀ :=
    Tstar_mem hk hν u₀
  have hle : sSup (persistSet hk ν u₀) ≤
      localTime ν (incl (three_le_succ hk) u₀) :=
    csSup_le hSne fun t ht => ht.some.le_T3
  have hEq : sSup (persistSet hk ν u₀) =
      localTime ν (incl (three_le_succ hk) u₀) := by
    refine le_antisymm hle ?_
    by_contra hlt
    have hlt' : sSup (persistSet hk ν u₀) <
        localTime ν (incl (three_le_succ hk) u₀) := lt_of_not_ge hlt
    obtain ⟨W⟩ := hmem
    obtain ⟨δstar, hδstar_pos, hrest⟩ := persist_restart_window hk hν u₀
    obtain ⟨τ, hτge, hτ0, hτmem⟩ := hrest W
    have hτpos : 0 < τ :=
      lt_of_lt_of_le (lt_min hδstar_pos (sub_pos.2 hlt')) hτge
    have : sSup (persistSet hk ν u₀) < sSup (persistSet hk ν u₀) :=
      lt_of_lt_of_le (lt_add_of_pos_right _ hτpos) (le_csSup hSbd hτmem)
    exact this.false
  have hmemT : localTime ν (incl (three_le_succ hk) u₀) ∈ persistSet hk ν u₀ :=
    hEq ▸ hmem
  obtain ⟨W⟩ := hmemT
  refine ⟨W.path, ?_, isMild_inclMap hk hν W.nonneg u₀ W.mild,
    inclMap_mem_ball hk (rad_nonneg _) W.inclBound⟩
  convert W.mild

#print axioms PersistenceHm.persist_restart_window
#print axioms PersistenceHm.Tstar_mem
#print axioms PersistenceHm.persist_on_H3_time
end PersistenceHm
