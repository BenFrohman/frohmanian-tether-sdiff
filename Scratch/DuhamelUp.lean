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

end DuhamelUp

#print axioms DuhamelUp.intervalIntegrable_upI
#print axioms DuhamelUp.norm_duhUp_le
#print axioms DuhamelUp.duhUp_sub
#print axioms DuhamelUp.continuous_duh
