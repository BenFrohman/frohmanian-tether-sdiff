import Scratch.Duhamel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-! # Smoothing Duhamel estimate `Ĥ^m → Ĥ^{m+1}` and continuity of the Duhamel integral

`‖∫₀ᵗ e^{(t-s)Δ} G(s) ds‖_{Ĥ^{m+1}} ≤ M (t + 2√t)` when `‖G(s)‖_{Ĥ^m} ≤ M` on `[0,t]`. -/

open MeasureTheory FourierTransform Real Filter Topology Set
open scoped ENNReal

noncomputable section
namespace DuhamelUp

open LerayHeat SobolevFourier HeatSobolev SobolevHilbert Duhamel

variable {m : ℕ}

lemma coeFn_heatUp {τ : ℝ} (hτ : 0 < τ) (G : Hm m) :
    (heatUp m hτ G : E3 → V) =ᵐ[μw (m + 1)] fun ξ => ((gauss τ ξ : ℝ) : ℂ) • (G : E3 → V) ξ :=
  coeFn_wmul (heatSym τ) (heatSym_meas τ) _ (by positivity) (bound_up m hτ) G

/-- `e^{τΔ} = e^{(τ-σ)Δ} e^{σΔ}` across `Ĥ^m → Ĥ^{m+1}`. -/
lemma heatUp_eq {σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) (h : σ ≤ τ) (G : Hm m) :
    heatUp m hτ G = heatH (m + 1) (τ - σ) (heatUp m hσ G) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_heatUp hτ G, coeFn_heatH (τ - σ) (heatUp m hσ G), coeFn_heatUp hσ G]
    with ξ h1 h2 h3
  rw [h1, h2, h3, smul_smul, ← Complex.ofReal_mul, gauss_mul (sub_nonneg.2 h) hσ.le, sub_add_cancel]

/-- Smoothing Duhamel integrand (`0` at and after `s = t`). -/
def upI (G : ℝ → Hm m) (t s : ℝ) : Hm (m + 1) :=
  if h : s < t then heatUp m (sub_pos.2 h) (G s) else 0

lemma continuousOn_upI {G : ℝ → Hm m} (hG : Continuous G) (t : ℝ) :
    ContinuousOn (upI G t) (Iio t) := by
  intro s0 hs0
  have hs0' : s0 < t := hs0
  set σ := (t - s0) / 2
  have hσ : 0 < σ := by simp only [σ]; linarith
  have hc : Continuous fun s => heatH (m + 1) ((t - s) - σ) (heatUp m hσ (G s)) :=
    continuous_heatH_comp ((continuous_const.sub continuous_id).sub continuous_const)
      ((heatUp m hσ).continuous.comp hG)
  refine (ContinuousAt.congr hc.continuousAt ?_).continuousWithinAt
  have : ∀ᶠ s in 𝓝 s0, s < s0 + σ := eventually_lt_nhds (by linarith)
  filter_upwards [this] with s hs
  have hst : s < t := by simp only [σ] at hs; linarith
  simp only [upI, dif_pos hst]
  exact (heatUp_eq hσ (sub_pos.2 hst) (by simp only [σ] at hs ⊢; linarith) (G s)).symm

lemma sqrt_le_one_add_rpow {u : ℝ} (hu : 0 < u) :
    Real.sqrt (1 + 1 / (2 * u)) ≤ 1 + u ^ (-(1 / 2 : ℝ)) := by
  have ha : 0 ≤ u ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hu.le _
  have hsq : (u ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / u := by
    have e : (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 := by norm_num
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le, e, Real.rpow_neg_one, one_div]
  rw [Real.sqrt_le_left (by positivity)]
  have : 1 / (2 * u) ≤ 1 / u := by
    rw [div_le_div_iff₀ (by positivity) hu]; linarith
  nlinarith

lemma norm_upI_le {G : ℝ → Hm m} {t M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ s ∈ Icc 0 t, ‖G s‖ ≤ M)
    {s : ℝ} (hs : s ∈ Icc 0 t) : ‖upI G t s‖ ≤ M * (1 + (t - s) ^ (-(1 / 2 : ℝ))) := by
  unfold upI
  split_ifs with h
  · refine (norm_heatUp_le m (sub_pos.2 h) (G s)).trans ?_
    rw [mul_comm M]
    exact mul_le_mul (sqrt_le_one_add_rpow (sub_pos.2 h)) (hM s hs) (norm_nonneg _)
      (by positivity [Real.rpow_nonneg (sub_pos.2 h).le (-(1 / 2 : ℝ))])
  · rw [norm_zero]
    have : 0 ≤ (t - s) ^ (-(1 / 2 : ℝ)) := by
      rcases le_or_gt 0 (t - s) with h' | h'
      · exact Real.rpow_nonneg h' _
      · exfalso; exact h (by linarith [hs.2])
    positivity

lemma intervalIntegrable_rp (t : ℝ) :
    IntervalIntegrable (fun s => (t - s) ^ (-(1 / 2 : ℝ))) volume 0 t := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t)
    (by norm_num : (-1 : ℝ) < -(1 / 2))).comp_sub_left t
  simp only [sub_zero, sub_self] at h
  exact h.symm

lemma intervalIntegrable_bound (M t : ℝ) :
    IntervalIntegrable (fun s => M * (1 + (t - s) ^ (-(1 / 2 : ℝ)))) volume 0 t :=
  ((intervalIntegrable_const (c := (1 : ℝ))).add (intervalIntegrable_rp t)).const_mul M

lemma integral_bound {t : ℝ} (ht : 0 ≤ t) (M : ℝ) :
    ∫ s in (0 : ℝ)..t, M * (1 + (t - s) ^ (-(1 / 2 : ℝ))) = M * (t + 2 * Real.sqrt t) := by
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add intervalIntegrable_const
    (intervalIntegrable_rp t)]
  rw [intervalIntegral.integral_comp_sub_left (fun x => x ^ (-(1 / 2 : ℝ))),
    integral_rpow (Or.inl (by norm_num))]
  simp only [sub_self, sub_zero, intervalIntegral.integral_const, smul_eq_mul, mul_one]
  rw [Real.zero_rpow (by norm_num), Real.sqrt_eq_rpow]
  norm_num
  left; ring

/-- The smoothing Duhamel integrand is integrable on `[0, t]`. -/
theorem intervalIntegrable_upI {G : ℝ → Hm m} (hG : Continuous G) {t M : ℝ} (ht : 0 ≤ t)
    (hM0 : 0 ≤ M) (hM : ∀ s ∈ Icc 0 t, ‖G s‖ ≤ M) :
    IntervalIntegrable (upI G t) volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht]
  have hb := (intervalIntegrable_iff_integrableOn_Ioo_of_le ht).1 (intervalIntegrable_bound M t)
  refine hb.mono' ?_ ?_
  · exact ((continuousOn_upI hG t).mono Ioo_subset_Iio_self).aestronglyMeasurable measurableSet_Ioo
  · refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun s hs => ?_)
    exact norm_upI_le hM0 hM (Ioo_subset_Icc_self hs)

/-- Smoothing Duhamel integral `∫₀ᵗ e^{(t-s)Δ} G(s) ds ∈ Ĥ^{m+1}`. -/
def duhUp (m : ℕ) (G : ℝ → Hm m) (t : ℝ) : Hm (m + 1) := ∫ s in (0 : ℝ)..t, upI G t s

/-- **Smoothing Duhamel estimate**: `‖∫₀ᵗ e^{(t-s)Δ}G‖_{Ĥ^{m+1}} ≤ M (t + 2√t)` when
`‖G‖_{Ĥ^m} ≤ M` on `[0,t]`. -/
theorem norm_duhUp_le {G : ℝ → Hm m} (hG : Continuous G) {t M : ℝ} (ht : 0 ≤ t) (hM0 : 0 ≤ M)
    (hM : ∀ s ∈ Icc 0 t, ‖G s‖ ≤ M) : ‖duhUp m G t‖ ≤ M * (t + 2 * Real.sqrt t) := by
  unfold duhUp
  refine (intervalIntegral.norm_integral_le_integral_norm ht).trans ?_
  rw [← integral_bound ht M]
  exact intervalIntegral.integral_mono_on ht (intervalIntegrable_upI hG ht hM0 hM).norm
    (intervalIntegrable_bound M t) fun s hs => norm_upI_le hM0 hM hs

/-- `duhUp` is linear in `G` (difference form). -/
theorem duhUp_sub {G H : ℝ → Hm m} (hG : Continuous G) (hH : Continuous H) {t MG MH : ℝ}
    (ht : 0 ≤ t) (hMG0 : 0 ≤ MG) (hMG : ∀ s ∈ Icc 0 t, ‖G s‖ ≤ MG) (hMH0 : 0 ≤ MH)
    (hMH : ∀ s ∈ Icc 0 t, ‖H s‖ ≤ MH) :
    duhUp m G t - duhUp m H t = duhUp m (fun s => G s - H s) t := by
  unfold duhUp
  rw [← intervalIntegral.integral_sub (intervalIntegrable_upI hG ht hMG0 hMG)
    (intervalIntegrable_upI hH ht hMH0 hMH)]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [upI]
  split_ifs <;> simp [map_sub]

/-- Continuity of the (non-smoothing) Duhamel integral in `t`. -/
theorem continuous_duh {G : ℝ → Hm m} (hG : Continuous G) : Continuous (duh m G) := by
  unfold duh
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun t s => heatH m (t - s) (G s))
    (continuous_heatH_comp (continuous_fst.sub continuous_snd) (hG.comp continuous_snd))
    continuous_id

/-! ## Continuity of the smoothing Duhamel integral in `t` -/

/-- Kernel in the variable `r = t - s`. -/
def kf (G : ℝ → Hm m) (t r : ℝ) : Hm (m + 1) := if h : 0 < r then heatUp m h (G (t - r)) else 0

/-- Truncated kernel `1_{r < t} kf t r`. -/
def kt (G : ℝ → Hm m) (t : ℝ) : ℝ → Hm (m + 1) := (Iio t).indicator (kf G t)

lemma continuousOn_heatUp_r (x : ℝ → Hm m) (hx : Continuous x) :
    ContinuousOn (fun r => if h : 0 < r then heatUp m h (x r) else 0) (Ioi 0) := by
  intro r0 hr0
  have hr0' : 0 < r0 := hr0
  set σ := r0 / 2
  have hσ : 0 < σ := by simp only [σ]; linarith
  have hc : Continuous fun r => heatH (m + 1) (r - σ) (heatUp m hσ (x r)) :=
    continuous_heatH_comp (continuous_id.sub continuous_const) ((heatUp m hσ).continuous.comp hx)
  refine (ContinuousAt.congr hc.continuousAt ?_).continuousWithinAt
  filter_upwards [eventually_gt_nhds (show σ < r0 by simp only [σ]; linarith)] with r hr
  have hr' : 0 < r := hσ.trans hr
  simp only [dif_pos hr']
  exact (heatUp_eq hσ hr' hr.le (x r)).symm

lemma norm_kt_le {G : ℝ → Hm m} {T M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ s ∈ Icc 0 T, ‖G s‖ ≤ M)
    {t r : ℝ} (ht : t ∈ Icc 0 T) (hr : r ∈ Ioc 0 T) : ‖kt G t r‖ ≤ M * (1 + r ^ (-(1 / 2 : ℝ))) := by
  have hb : 0 ≤ M * (1 + r ^ (-(1 / 2 : ℝ))) := by
    have := Real.rpow_nonneg hr.1.le (-(1 / 2 : ℝ)); positivity
  unfold kt
  by_cases hrt : r < t
  · rw [indicator_of_mem (show r ∈ Iio t from hrt)]
    simp only [kf, dif_pos hr.1]
    refine (norm_heatUp_le m hr.1 _).trans ?_
    rw [mul_comm M]
    exact mul_le_mul (sqrt_le_one_add_rpow hr.1) (hM _ ⟨by linarith, by linarith [ht.2, hr.1]⟩)
      (norm_nonneg _) (by have := Real.rpow_nonneg hr.1.le (-(1 / 2 : ℝ)); positivity)
  · rw [indicator_of_notMem (show r ∉ Iio t from hrt), norm_zero]; exact hb

lemma duhUp_eq_kt {G : ℝ → Hm m} (hG : Continuous G) {T M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ s ∈ Icc 0 T, ‖G s‖ ≤ M) {t : ℝ} (ht : t ∈ Icc 0 T) :
    duhUp m G t = ∫ r in (0 : ℝ)..T, kt G t r := by
  unfold duhUp
  have e1 : ∫ s in (0 : ℝ)..t, upI G t s = ∫ s in (0 : ℝ)..t, kf G t (t - s) := by
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [upI, kf, sub_sub_cancel, sub_pos]
  rw [e1, intervalIntegral.integral_comp_sub_left (fun r => kf G t r), sub_self, sub_zero]
  have hint : IntervalIntegrable (kt G t) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (ht.1.trans ht.2)]
    have hb := (intervalIntegrable_iff_integrableOn_Ioc_of_le (ht.1.trans ht.2)).1
      (((intervalIntegrable_const (c := (1 : ℝ))).add
        (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := T)
          (by norm_num : (-1 : ℝ) < -(1 / 2)))).const_mul M)
    refine hb.mono' ?_ ?_
    · refine AEStronglyMeasurable.indicator ?_ measurableSet_Iio
      have hco := continuousOn_heatUp_r (m := m) (fun r => G (t - r))
        (hG.comp (continuous_const.sub continuous_id))
      exact (hco.mono (fun r hr => hr.1)).aestronglyMeasurable measurableSet_Ioc
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun r hr => ?_)
      exact norm_kt_le hM0 hM ht hr
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := t)
    (hint.mono_set (by rw [uIcc_of_le ht.1, uIcc_of_le (ht.1.trans ht.2)]; exact Icc_subset_Icc le_rfl ht.2))
    (hint.mono_set (by rw [uIcc_of_le ht.2, uIcc_of_le (ht.1.trans ht.2)]; exact Icc_subset_Icc ht.1 le_rfl))]
  have e2 : ∫ r in t..T, kt G t r = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : Hm (m + 1))) (fun r hr => ?_)]
    · simp
    · rw [uIcc_of_le ht.2] at hr
      exact indicator_of_notMem (s := Iio t) (f := kf G t) (fun h : r < t => absurd hr.1 (not_le.2 h))
  rw [e2, add_zero]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_singleton (μ := volume) t)] with r hrt hr
  rw [uIoc_of_le ht.1] at hr
  exact (indicator_of_mem (show r ∈ Iio t from lt_of_le_of_ne hr.2 hrt) _).symm

lemma aesm_kt {G : ℝ → Hm m} (hG : Continuous G) (t T : ℝ) :
    AEStronglyMeasurable (kt G t) (volume.restrict (Ioc 0 T)) := by
  refine AEStronglyMeasurable.indicator ?_ measurableSet_Iio
  have hco := continuousOn_heatUp_r (m := m) (fun r => G (t - r))
    (hG.comp (continuous_const.sub continuous_id))
  exact (hco.mono (fun r hr => hr.1)).aestronglyMeasurable measurableSet_Ioc

lemma continuous_kf_t {G : ℝ → Hm m} (hG : Continuous G) (r : ℝ) :
    Continuous fun t => kf G t r := by
  by_cases hr : 0 < r
  · simp only [kf, dif_pos hr]
    exact (heatUp m hr).continuous.comp (hG.comp (continuous_id.sub continuous_const))
  · simp only [kf, dif_neg hr]; exact continuous_const

/-- **Continuity in `t`** of the smoothing Duhamel integral on `[0, T]`. -/
theorem continuousOn_duhUp {G : ℝ → Hm m} (hG : Continuous G) {T M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ s ∈ Icc 0 T, ‖G s‖ ≤ M) : ContinuousOn (duhUp m G) (Icc 0 T) := by
  intro t0 ht0
  have hT : 0 ≤ T := ht0.1.trans ht0.2
  refine ContinuousWithinAt.congr (f := fun t => ∫ r in (0 : ℝ)..T, kt G t r) ?_
    (fun t ht => duhUp_eq_kt hG hM0 hM ht) (duhUp_eq_kt hG hM0 hM ht0)
  refine intervalIntegral.continuousWithinAt_of_dominated_interval
    (bound := fun r => M * (1 + r ^ (-(1 / 2 : ℝ)))) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun t => ?_
    rw [uIoc_of_le hT]; exact aesm_kt hG t T
  · filter_upwards [self_mem_nhdsWithin] with t ht
    refine Eventually.of_forall fun r hr => ?_
    rw [uIoc_of_le hT] at hr
    exact norm_kt_le hM0 hM ht hr
  · exact ((intervalIntegrable_const (c := (1 : ℝ))).add
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := T)
        (by norm_num : (-1 : ℝ) < -(1 / 2)))).const_mul M
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_singleton (μ := volume) t0)]
      with r hr _
    refine ContinuousAt.continuousWithinAt ?_
    rcases lt_or_gt_of_ne (show r ≠ t0 from hr) with h | h
    · refine ((continuous_kf_t hG r).continuousAt).congr ?_
      filter_upwards [eventually_gt_nhds h] with t ht
      exact (indicator_of_mem (show r ∈ Iio t from ht) _).symm
    · refine (continuousAt_const (y := (0 : Hm (m + 1)))).congr ?_
      filter_upwards [eventually_lt_nhds h] with t ht
      exact (indicator_of_notMem (s := Iio t) (f := kf G t)
        (show r ∉ Iio t from fun h' => absurd (h'.trans ht) (lt_irrefl r))).symm

end DuhamelUp

#print axioms DuhamelUp.intervalIntegrable_upI
#print axioms DuhamelUp.norm_duhUp_le
#print axioms DuhamelUp.duhUp_sub
#print axioms DuhamelUp.continuous_duh
#print axioms DuhamelUp.continuousOn_duhUp
