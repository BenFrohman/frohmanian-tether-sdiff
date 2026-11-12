import Scratch.HeatDeriv
import Scratch.MildExistence
import Scratch.DuhamelUp
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Time derivative of the same-space Duhamel integral

The same-space viscosity Duhamel integral is
`duhνSame ν G t = ∫₀ᵗ e^{ν(t-s)Δ} G(s) ds` in `Ĥ^m`.  Its one-sided
time derivative, for a source in `Ĥ^{m+2}`, is `G(t) + ν Δ(∫₀ᵗ e^{ν(t-s)Δ} G(s) ds)`,
obtained from the Duhamel cocycle, the heat-semigroup derivative in
`HeatDeriv`, and an averaging argument for the increment. -/

open MeasureTheory FourierTransform Real Filter Topology Set
open scoped ENNReal

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
namespace DuhamelDeriv

open LerayHeat SobolevFourier SobolevHilbert Duhamel DuhamelUp HeatDeriv MildExistence ProductHm

/-! ## Inclusion commutes with the heat semigroup -/

/-- The coeFn identity for `e^{τΔ}` on `Ĥ^{m+2}`, read in the weaker measure `μw m`. -/
lemma coeFn_heatH_ae_low (m : ℕ) (τ : ℝ) (G : Hm (m + 2)) :
    (heatH (m + 2) τ G : E3 → V) =ᵐ[μw m] fun ξ =>
      ((gauss τ ξ : ℝ) : ℂ) • (G : E3 → V) ξ :=
  (ac_ww (m + 2) m).ae_le (coeFn_heatH τ G)

lemma incl_heatH (m : ℕ) (τ : ℝ) (G : Hm (m + 2)) :
    incl (incl_le_add_two m) (heatH (m + 2) τ G) =
      heatH m τ (incl (incl_le_add_two m) G) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_incl (incl_le_add_two m) (heatH (m + 2) τ G),
    coeFn_heatH_ae_low m τ G,
    coeFn_heatH τ (incl (incl_le_add_two m) G),
    coeFn_incl (incl_le_add_two m) G] with ξ h1 h2 h3 h4
  rw [h1, h2, h3, h4]

/-! ## Same-space Duhamel cocycle -/

/-- `∫₀^{t0+τ} e^{(t0+τ-s)Δ} G(s) ds = e^{τΔ}(∫₀^{t0} e^{(t0-s)Δ} G(s) ds) + ∫₀^τ e^{(τ-σ)Δ} G(σ+t0) dσ`. -/
theorem duh_cocycle {m : ℕ} {G : ℝ → Hm m} (hG : Continuous G) {t0 τ : ℝ}
    (ht0 : 0 ≤ t0) (hτ : 0 ≤ τ) :
    duh m G (t0 + τ) = heatH m τ (duh m G t0) + duh m (fun s => G (s + t0)) τ := by
  rcases eq_or_lt_of_le hτ with hτ0 | hτpos
  · rw [← hτ0, add_zero, heatH_zero]
    unfold duh
    rw [intervalIntegral.integral_same, add_zero]
  have hint : IntervalIntegrable (fun s => heatH m ((t0 + τ) - s) (G s)) volume 0 (t0 + τ) :=
    (continuous_duh_integrand hG (t0 + τ)).intervalIntegrable _ _
  have h1 : IntervalIntegrable (fun s => heatH m ((t0 + τ) - s) (G s)) volume 0 t0 :=
    hint.mono_set (by
      rw [uIcc_of_le ht0, uIcc_of_le (add_nonneg ht0 hτ)]
      exact Icc_subset_Icc le_rfl (le_add_of_nonneg_right hτ))
  have h2 : IntervalIntegrable (fun s => heatH m ((t0 + τ) - s) (G s)) volume t0 (t0 + τ) :=
    hint.mono_set (by
      rw [uIcc_of_le (le_add_of_nonneg_right hτ), uIcc_of_le (add_nonneg ht0 hτ)]
      exact Icc_subset_Icc ht0 le_rfl)
  unfold duh
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have e1 : (∫ s in (0 : ℝ)..t0, heatH m ((t0 + τ) - s) (G s)) =
      heatH m τ (∫ s in (0 : ℝ)..t0, heatH m (t0 - s) (G s)) := by
    have hI0 : IntervalIntegrable (fun s => heatH m (t0 - s) (G s)) volume 0 t0 :=
      (continuous_duh_integrand hG t0).intervalIntegrable _ _
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm (heatH m τ) hI0]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_singleton (μ := volume) t0)]
      with s hs0 hs
    have hs' : s ∈ uIoc 0 t0 := hs
    rw [uIoc_of_le ht0] at hs'
    have hslt : s ≤ t0 := hs'.2
    have hτs : 0 ≤ t0 - s := sub_nonneg.2 hslt
    rw [heatH_heatH hτ hτs]
    have : τ + (t0 - s) = (t0 + τ) - s := by ring
    rw [this]
  have e2 : (∫ s in t0..(t0 + τ), heatH m ((t0 + τ) - s) (G s)) =
      ∫ σ in (0 : ℝ)..τ, heatH m (τ - σ) (G (σ + t0)) := by
    have hlim : (∫ s in t0..(t0 + τ), heatH m ((t0 + τ) - s) (G s)) =
        ∫ s in (0 + t0)..(τ + t0), heatH m ((t0 + τ) - s) (G s) := by
      rw [zero_add, add_comm t0 τ]
    rw [hlim, ← intervalIntegral.integral_comp_add_right
      (fun s => heatH m ((t0 + τ) - s) (G s)) t0]
    refine intervalIntegral.integral_congr fun σ _ => ?_
    have : (t0 + τ) - (σ + t0) = τ - σ := by ring
    simp only [this]
  rw [e1, e2]

/-- Same-space viscosity Duhamel integral `∫₀ᵗ e^{ν(t-s)Δ} G(s) ds` in `Ĥ^m`. -/
def duhνSame (m : ℕ) (ν : ℝ) (G : ℝ → Hm m) (t : ℝ) : Hm m :=
  duh m (scaleG ν G) (ν * t)

lemma duhνSame_cocycle {m : ℕ} {ν : ℝ} (hν : 0 < ν) {G : ℝ → Hm m} (hG : Continuous G)
    {t0 τ : ℝ} (ht0 : 0 ≤ t0) (hτ : 0 ≤ τ) :
    duhνSame m ν G (t0 + τ) =
      heatH m (ν * τ) (duhνSame m ν G t0) + duhνSame m ν (fun s => G (s + t0)) τ := by
  unfold duhνSame
  rw [mul_add, duh_cocycle (continuous_scaleG hG) (mul_nonneg hν.le ht0) (mul_nonneg hν.le hτ)]
  have hsh : (fun σ => scaleG ν G (σ + ν * t0)) = scaleG ν (fun s => G (s + t0)) := by
    funext σ
    simp only [scaleG, add_div, mul_div_cancel_left₀ _ hν.ne']
  rw [hsh]

lemma scaleG_incl (m : ℕ) (ν : ℝ) (G : ℝ → Hm (m + 2)) (σ : ℝ) :
    incl (incl_le_add_two m) (scaleG ν G σ) =
      scaleG ν (fun s => incl (incl_le_add_two m) (G s)) σ := by
  simp only [scaleG, map_smul]

lemma incl_duh (m : ℕ) {G : ℝ → Hm (m + 2)} (hG : Continuous G) (t : ℝ) :
    incl (incl_le_add_two m) (duh (m + 2) G t) =
      duh m (fun s => incl (incl_le_add_two m) (G s)) t := by
  unfold duh
  have hI : IntervalIntegrable (fun s => heatH (m + 2) (t - s) (G s)) volume 0 t :=
    (continuous_duh_integrand hG t).intervalIntegrable _ _
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm (incl (incl_le_add_two m)) hI]
  refine intervalIntegral.integral_congr fun s _ => ?_
  exact incl_heatH m (t - s) (G s)

lemma incl_duhνSame (m : ℕ) (ν : ℝ) {G : ℝ → Hm (m + 2)} (hG : Continuous G) (t : ℝ) :
    incl (incl_le_add_two m) (duhνSame (m + 2) ν G t) =
      duhνSame m ν (fun s => incl (incl_le_add_two m) (G s)) t := by
  unfold duhνSame
  rw [incl_duh m (continuous_scaleG hG)]
  congr 1
  funext σ
  exact scaleG_incl m ν G σ

/-! ## Averaging of the Duhamel increment -/

lemma duh_avg_sub {m : ℕ} {G : ℝ → Hm m} (hG : Continuous G) (t0 : ℝ) {h : ℝ}
    (hh : 0 < h) :
    h⁻¹ • duh m (fun s => G (s + t0)) h - G t0 =
      h⁻¹ • ∫ s in (0 : ℝ)..h,
        (heatH m (h - s) (G (s + t0)) - G t0) := by
  have hF : Continuous fun s => G (s + t0) :=
    hG.comp (continuous_id.add continuous_const)
  have hinter : Continuous fun s => heatH m (h - s) (G (s + t0)) :=
    continuous_duh_integrand hF h
  have hinterI : IntervalIntegrable (fun s => heatH m (h - s) (G (s + t0)))
      volume 0 h := hinter.intervalIntegrable _ _
  have hconst : (∫ _s in (0 : ℝ)..h, G t0) = h • G t0 := by
    rw [intervalIntegral.integral_const, sub_zero]
  unfold duh
  calc h⁻¹ • (∫ s in (0 : ℝ)..h, heatH m (h - s) (G (s + t0))) - G t0
      = h⁻¹ • (∫ s in (0 : ℝ)..h, heatH m (h - s) (G (s + t0))) -
          h⁻¹ • (h • G t0) := by
        rw [inv_smul_smul₀ hh.ne']
    _ = h⁻¹ • ((∫ s in (0 : ℝ)..h, heatH m (h - s) (G (s + t0))) - h • G t0) := by
        rw [smul_sub]
    _ = h⁻¹ • ((∫ s in (0 : ℝ)..h, heatH m (h - s) (G (s + t0))) -
          ∫ _s in (0 : ℝ)..h, G t0) := by
        rw [hconst]
    _ = h⁻¹ • ∫ s in (0 : ℝ)..h, (heatH m (h - s) (G (s + t0)) - G t0) := by
        rw [intervalIntegral.integral_sub hinterI intervalIntegrable_const]

lemma dist_pair_zero (a b : ℝ) : dist (a, b) ((0 : ℝ), 0) = max |a| |b| := by
  simp [Prod.dist_eq]

/-- A continuous real function vanishing at the origin is small on the
triangle `{(h-s,s) | 0 ≤ s ≤ h}` for small `h > 0`.  Isolated from the
`Ĥᵐ` types so the ball-membership argument does not time out. -/
lemma eventually_small_on_triangle {F : ℝ × ℝ → ℝ}
    (hF : Continuous F) (hF0 : F (0, 0) = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ d, 0 < d ∧ ∀ h, 0 < h → h < d → ∀ s ∈ Icc (0 : ℝ) h, F (h - s, s) < ε := by
  have htend : Tendsto F (𝓝 ((0 : ℝ), 0)) (𝓝 0) := by
    simpa [hF0] using hF.tendsto ((0 : ℝ), 0)
  have hnear : {p : ℝ × ℝ | F p < ε} ∈ 𝓝 ((0 : ℝ), 0) :=
    htend (Iio_mem_nhds hε)
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.1 hnear
  refine ⟨d, hd, fun h hh hlt s hs => ?_⟩
  have hdist : dist (h - s, s) ((0 : ℝ), 0) < d := by
    rw [dist_pair_zero, abs_of_nonneg (sub_nonneg.2 hs.2), abs_of_nonneg hs.1]
    exact max_lt (lt_of_le_of_lt (sub_le_self h hs.1) hlt)
      (lt_of_le_of_lt hs.2 hlt)
  exact hball hdist

/-- If the heat increment is uniformly `≤ ε` on `[0,h]`, the Duhamel average is `≤ ε`. -/
lemma norm_duh_avg_le {m : ℕ} {G : ℝ → Hm m} (hG : Continuous G) (t0 : ℝ)
    {h ε : ℝ} (hh : 0 < h) (_hε : 0 ≤ ε)
    (hbd : ∀ s ∈ Icc (0 : ℝ) h,
      ‖heatH m (h - s) (G (s + t0)) - G t0‖ ≤ ε) :
    ‖h⁻¹ • duh m (fun s => G (s + t0)) h - G t0‖ ≤ ε := by
  have hF : Continuous fun s => G (s + t0) :=
    hG.comp (continuous_id.add continuous_const)
  have hinter : Continuous fun s => heatH m (h - s) (G (s + t0)) :=
    continuous_duh_integrand hF h
  have hsub : Continuous fun s => heatH m (h - s) (G (s + t0)) - G t0 :=
    hinter.sub continuous_const
  rw [duh_avg_sub hG t0 hh]
  refine (norm_smul_le _ _).trans ?_
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hh)]
  have hint :=
    (intervalIntegral.norm_integral_le_integral_norm (le_of_lt hh)).trans
      (intervalIntegral.integral_mono_on (le_of_lt hh)
        (hsub.norm.intervalIntegrable (μ := volume) 0 h)
        (intervalIntegrable_const (μ := volume)) hbd)
  refine (mul_le_mul_of_nonneg_left hint (inv_nonneg.2 hh.le)).trans ?_
  have : (∫ _s in (0 : ℝ)..h, ε) = h * ε := by
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  rw [this, ← mul_assoc, inv_mul_cancel₀ hh.ne', one_mul]

/-- The increment average `(1/h) ∫₀ʰ e^{(h-s)Δ} G(t0+s) ds` tends to `G(t0)` as `h ↓ 0`. -/
lemma tendsto_duh_avg {m : ℕ} {G : ℝ → Hm m} (hG : Continuous G) (t0 : ℝ) :
    Tendsto (fun h : ℝ => h⁻¹ • duh m (fun s => G (s + t0)) h)
      (𝓝[>] (0 : ℝ)) (𝓝 (G t0)) := by
  have hc : Continuous fun p : ℝ × ℝ => heatH m p.1 (G (p.2 + t0)) :=
    continuous_heatH_comp continuous_fst
      (hG.comp (continuous_snd.add continuous_const))
  have hFn : Continuous fun p : ℝ × ℝ => ‖heatH m p.1 (G (p.2 + t0)) - G t0‖ :=
    (hc.sub continuous_const).norm
  have hF0 : (fun p : ℝ × ℝ => ‖heatH m p.1 (G (p.2 + t0)) - G t0‖) (0, 0) = 0 := by
    simp [heatH_zero]
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨d, hd, htri⟩ := eventually_small_on_triangle hFn hF0 hε2
  filter_upwards [eventually_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hd)] with h hhIoi hhd
  have hh : 0 < h := mem_Ioi.1 hhIoi
  have hbd : ∀ s ∈ Icc (0 : ℝ) h,
      ‖heatH m (h - s) (G (s + t0)) - G t0‖ ≤ ε / 2 :=
    fun s hs => (htri h hh hhd s hs).le
  rw [Real.dist_eq, sub_zero, abs_norm]
  exact lt_of_le_of_lt (norm_duh_avg_le hG t0 hh (le_of_lt hε2) hbd) (half_lt_self hε)

lemma scaleG_apply_mul {m : ℕ} {ν : ℝ} (hν : 0 < ν) (G : ℝ → Hm m) (t0 : ℝ) :
    ν • scaleG ν G (ν * t0) = G t0 := by
  unfold scaleG
  rw [mul_div_cancel_left₀ _ hν.ne']
  change (ν : ℂ) • ((ν⁻¹ : ℝ) : ℂ) • G t0 = G t0
  rw [Complex.ofReal_inv, smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 hν.ne'),
    one_smul]

/-- Viscosity-scaled increment average tends to `G(t0)` as `h ↓ 0`. -/
lemma tendsto_duhνSame_avg {m : ℕ} {ν : ℝ} (hν : 0 < ν) {G : ℝ → Hm m}
    (hG : Continuous G) (t0 : ℝ) :
    Tendsto (fun h : ℝ => h⁻¹ • duhνSame m ν (fun s => G (s + t0)) h)
      (𝓝[>] (0 : ℝ)) (𝓝 (G t0)) := by
  have hsh : scaleG ν (fun s => G (s + t0)) = fun σ => scaleG ν G (σ + ν * t0) := by
    funext σ
    simp only [scaleG, add_div, mul_div_cancel_left₀ _ hν.ne']
  have havg := tendsto_duh_avg (continuous_scaleG (ν := ν) hG) (ν * t0)
  have hmul_nhds : Tendsto (fun h : ℝ => ν * h) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h0 : Tendsto (fun h : ℝ => ν * h) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa using (continuous_const_mul ν).tendsto (0 : ℝ)
    exact h0.mono_left nhdsWithin_le_nhds
  have hmul : Tendsto (fun h : ℝ => ν * h) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hmul_nhds
      (eventually_mem_nhdsWithin.mono fun h hh => mul_pos hν (mem_Ioi.1 hh))
  have hRHS := (havg.comp hmul).const_smul ν
  have hlim : ν • scaleG ν G (ν * t0) = G t0 := scaleG_apply_mul hν G t0
  rw [hlim] at hRHS
  have hrew : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
      ν • ((ν * h)⁻¹ • duh m (fun σ => scaleG ν G (σ + ν * t0)) (ν * h)) =
        h⁻¹ • duhνSame m ν (fun s => G (s + t0)) h := by
    filter_upwards [eventually_mem_nhdsWithin] with h hh
    have hhpos : 0 < h := mem_Ioi.1 hh
    unfold duhνSame
    rw [hsh]
    have : h⁻¹ = ν * (ν * h)⁻¹ := by
      field_simp [hν.ne', hhpos.ne']
    rw [this, mul_smul]
  exact hRHS.congr' hrew

lemma duh_zero {m : ℕ} (G : ℝ → Hm m) : duh m G 0 = 0 := by
  unfold duh
  rw [intervalIntegral.integral_same]

lemma duhνSame_zero {m : ℕ} (ν : ℝ) (G : ℝ → Hm m) : duhνSame m ν G 0 = 0 := by
  unfold duhνSame
  rw [mul_zero, duh_zero]

/-- Translating a right derivative at `0` along `Ici 0` gives a right
derivative at `t0` along `Ici t0`. -/
lemma hasDerivWithinAt_Ici_translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {f' : E} {t0 : ℝ}
    (hf : HasDerivWithinAt (fun τ => f (t0 + τ)) f' (Ici (0 : ℝ)) 0) :
    HasDerivWithinAt f f' (Ici t0) t0 := by
  have hh : HasDerivWithinAt (fun t : ℝ => t - t0) (1 : ℝ) (Ici t0) t0 := by
    simpa using ((hasDerivAt_id t0).sub_const t0).hasDerivWithinAt (s := Ici t0)
  have hmaps : MapsTo (fun t : ℝ => t - t0) (Ici t0) (Ici (0 : ℝ)) :=
    fun t ht => sub_nonneg.2 (mem_Ici.1 ht)
  have hcomp := hf.scomp_of_eq t0 hh hmaps (by rw [sub_self])
  have heq : (fun τ => f (t0 + τ)) ∘ (fun t : ℝ => t - t0) = f := by
    ext t
    simp
  rw [heq, one_smul] at hcomp
  exact hcomp

/-- Right derivative of the same-space viscosity Duhamel integral along `Ici t0`.
For a continuous source in `Ĥ^{m+2}` the derivative in `Ĥ^m` is
`G(t0) + ν Δ(∫₀^{t0} e^{ν(t0-s)Δ} G(s) ds)`. -/
theorem hasDerivWithinAt_duhνSame_Ici
    {m : ℕ} {ν : ℝ} (hν : 0 < ν) {G : ℝ → Hm (m + 2)} (hG : Continuous G)
    {t0 : ℝ} (ht0 : 0 ≤ t0) :
    HasDerivWithinAt
      (fun t => duhνSame m ν (fun s => incl (incl_le_add_two m) (G s)) t)
      (incl (incl_le_add_two m) (G t0) +
        ν • lapH m (duhνSame (m + 2) ν G t0))
      (Ici t0) t0 := by
  set Glow : ℝ → Hm m := fun s => incl (incl_le_add_two m) (G s)
  have hGlow : Continuous Glow := (incl (incl_le_add_two m)).continuous.comp hG
  set Ih : ℝ → Hm (m + 2) := duhνSame (m + 2) ν G
  set Il : ℝ → Hm m := duhνSame m ν Glow
  refine hasDerivWithinAt_Ici_translate ?_
  have hcocycle : EqOn (fun τ => Il (t0 + τ))
      (fun τ => heatOfHigh m (Ih t0) (ν * τ) +
        duhνSame m ν (fun s => Glow (s + t0)) τ)
      (Ici (0 : ℝ)) := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := mem_Ici.1 hτ
    change duhνSame m ν Glow (t0 + τ) =
      heatOfHigh m (duhνSame (m + 2) ν G t0) (ν * τ) +
        duhνSame m ν (fun s => Glow (s + t0)) τ
    rw [duhνSame_cocycle hν hGlow ht0 hτ0]
    congr 1
    rw [heatOfHigh, incl_duhνSame m ν hG t0]
  have hheat : HasDerivWithinAt (fun σ => heatOfHigh m (Ih t0) (ν * σ))
      (ν • heatH m (ν * 0) (lapH m (Ih t0))) (Ici (0 : ℝ)) 0 :=
    hasDerivWithinAt_heatH_visc m ν hν.le (Ih t0) le_rfl
  have hheat' : HasDerivWithinAt (fun σ => heatOfHigh m (Ih t0) (ν * σ))
      (ν • lapH m (Ih t0)) (Ici (0 : ℝ)) 0 := by
    simpa [mul_zero, heatH_zero] using hheat
  have havg : HasDerivWithinAt
      (fun τ => duhνSame m ν (fun s => Glow (s + t0)) τ)
      (Glow t0) (Ici (0 : ℝ)) 0 := by
    rw [hasDerivWithinAt_iff_tendsto_slope]
    have hset : (Ici (0 : ℝ)) \ {0} = Ioi (0 : ℝ) := by
      ext x
      constructor
      · intro hx
        exact lt_of_le_of_ne (mem_Ici.1 hx.1) (Ne.symm hx.2)
      · intro hx
        exact ⟨mem_Ici.2 hx.le, hx.ne'⟩
    rw [hset]
    have hT := tendsto_duhνSame_avg hν hGlow t0
    refine hT.congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with h _hh
    rw [slope_def_module, sub_zero, duhνSame_zero, sub_zero]
  have hsum := hheat'.add havg
  have hsum' : HasDerivWithinAt
      (fun τ => heatOfHigh m (Ih t0) (ν * τ) +
        duhνSame m ν (fun s => Glow (s + t0)) τ)
      (Glow t0 + ν • lapH m (Ih t0)) (Ici (0 : ℝ)) 0 := by
    convert hsum using 1
    exact add_comm _ _
  exact hsum'.congr_of_mem (fun τ hτ => hcocycle hτ) self_mem_Ici

/-! ## Inclusion of the smoothing Duhamel integral -/

/-- The coeFn identity for the smoothing heat kernel, read in the weaker measure `μw m`. -/
lemma coeFn_heatUp_ae_low (m : ℕ) {τ : ℝ} (hτ : 0 < τ) (G : Hm m) :
    (heatUp m hτ G : E3 → V) =ᵐ[μw m] fun ξ =>
      ((gauss τ ξ : ℝ) : ℂ) • (G : E3 → V) ξ :=
  (ac_ww (m + 1) m).ae_le (coeFn_heatUp hτ G)

/-- Inclusion `Ĥ^{m+1} ↪ Ĥ^m` turns the smoothing heat kernel into the same-space one. -/
lemma incl_heatUp_to_heatH (m : ℕ) {τ : ℝ} (hτ : 0 < τ) (G : Hm m) :
    incl (Nat.le_succ m) (heatUp m hτ G) = heatH m τ G := by
  refine Lp.ext ?_
  filter_upwards [coeFn_incl (Nat.le_succ m) (heatUp m hτ G),
    coeFn_heatUp_ae_low m hτ G, coeFn_heatH τ G] with ξ h1 h2 h3
  rw [h1, h2, h3]

lemma incl_upI_to_heatH (m : ℕ) (G : ℝ → Hm m) {t s : ℝ} (hst : s < t) :
    incl (Nat.le_succ m) (upI G t s) = heatH m (t - s) (G s) := by
  unfold upI
  rw [dif_pos hst, incl_heatUp_to_heatH]

lemma exists_norm_bound_Icc {E : Type*} [NormedAddCommGroup E] {G : ℝ → E}
    (hG : Continuous G) {t : ℝ} (ht : 0 ≤ t) :
    ∃ M, 0 ≤ M ∧ ∀ s ∈ Icc (0 : ℝ) t, ‖G s‖ ≤ M := by
  have hC : ContinuousOn (fun s => ‖G s‖) (Icc (0 : ℝ) t) := hG.norm.continuousOn
  obtain ⟨s, hs, hmax⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_isMaxOn (nonempty_Icc.2 ht) hC
  exact ⟨‖G s‖, norm_nonneg _, fun x hx => hmax hx⟩

/-- Inclusion turns the smoothing Duhamel integral into the same-space Duhamel integral. -/
lemma incl_duhUp_to_duh (m : ℕ) {G : ℝ → Hm m} (hG : Continuous G) {t : ℝ} (ht : 0 ≤ t) :
    incl (Nat.le_succ m) (duhUp m G t) = duh m G t := by
  rcases eq_or_lt_of_le ht with ht0 | htpos
  · rw [← ht0]
    unfold duhUp duh
    rw [intervalIntegral.integral_same, intervalIntegral.integral_same, map_zero]
  obtain ⟨M, hM0, hM⟩ := exists_norm_bound_Icc hG ht
  have hIup : IntervalIntegrable (upI G t) volume 0 t :=
    intervalIntegrable_upI hG ht hM0 hM
  unfold duhUp duh
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm (incl (Nat.le_succ m)) hIup]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_singleton (μ := volume) t)]
    with s hs0 hs
  have hs' : s ∈ uIoc 0 t := hs
  rw [uIoc_of_le ht] at hs'
  have hslt : s < t := lt_of_le_of_ne hs'.2 hs0
  exact incl_upI_to_heatH m G hslt

/-- Inclusion turns the viscosity-scaled smoothing Duhamel integral into `duhνSame`. -/
lemma incl_duhν_to_duhνSame (m : ℕ) {ν t : ℝ} (hνt : 0 ≤ ν * t) {G : ℝ → Hm m} (hG : Continuous G) :
    incl (Nat.le_succ m) (duhν m ν G t) = duhνSame m ν G t := by
  unfold duhν duhνSame
  exact incl_duhUp_to_duh m (continuous_scaleG hG) hνt


/-- The coeFn of an inclusion, read in a still weaker measure. Isolated to avoid timeouts. -/
lemma coeFn_incl_ae_low {m m' m'' : ℕ} (h1 : m' ≤ m) (_h2 : m'' ≤ m') (F : Hm m) :
    (incl h1 F : E3 → V) =ᵐ[μw m''] (F : E3 → V) :=
  (ac_ww m' m'').ae_le (coeFn_incl h1 F)

lemma incl_comp {m m' m'' : ℕ} (h1 : m' ≤ m) (h2 : m'' ≤ m') (F : Hm m) :
    incl h2 (incl h1 F) = incl (le_trans h2 h1) F := by
  refine Lp.ext ?_
  filter_upwards [coeFn_incl h2 (incl h1 F), coeFn_incl_ae_low h1 h2 F,
    coeFn_incl (le_trans h2 h1) F] with ξ hA hB hC
  rw [hA, hB, hC]

lemma coeFn_heatH_ae_of_le {m m' : ℕ} (_hle : m' ≤ m) (τ : ℝ) (G : Hm m) :
    (heatH m τ G : E3 → V) =ᵐ[μw m'] fun ξ =>
      ((gauss τ ξ : ℝ) : ℂ) • (G : E3 → V) ξ :=
  (ac_ww m m').ae_le (coeFn_heatH τ G)

/-- Inclusion commutes with the heat semigroup for a general index drop. -/
lemma incl_heatH_of_le {m m' : ℕ} (hle : m' ≤ m) (τ : ℝ) (G : Hm m) :
    incl hle (heatH m τ G) = heatH m' τ (incl hle G) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_incl hle (heatH m τ G), coeFn_heatH_ae_of_le hle τ G,
    coeFn_heatH τ (incl hle G), coeFn_incl hle G] with ξ h1 h2 h3 h4
  rw [h1, h2, h3, h4]

lemma incl_duh_of_le {m m' : ℕ} (hle : m' ≤ m) {G : ℝ → Hm m} (hG : Continuous G) (t : ℝ) :
    incl hle (duh m G t) = duh m' (fun s => incl hle (G s)) t := by
  unfold duh
  have hI : IntervalIntegrable (fun s => heatH m (t - s) (G s)) volume 0 t :=
    (continuous_duh_integrand hG t).intervalIntegrable _ _
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm (incl hle) hI]
  refine intervalIntegral.integral_congr fun s _ => ?_
  exact incl_heatH_of_le hle (t - s) (G s)

lemma scaleG_incl_of_le {m m' : ℕ} (hle : m' ≤ m) (ν : ℝ) (G : ℝ → Hm m) (σ : ℝ) :
    incl hle (scaleG ν G σ) = scaleG ν (fun s => incl hle (G s)) σ := by
  simp only [scaleG, map_smul]

lemma incl_duhνSame_of_le {m m' : ℕ} (hle : m' ≤ m) (ν : ℝ)
    {G : ℝ → Hm m} (hG : Continuous G) (t : ℝ) :
    incl hle (duhνSame m ν G t) = duhνSame m' ν (fun s => incl hle (G s)) t := by
  unfold duhνSame
  rw [incl_duh_of_le hle (continuous_scaleG hG)]
  congr 1
  funext σ
  exact scaleG_incl_of_le hle ν G σ

#print axioms DuhamelDeriv.coeFn_heatH_ae_low
#print axioms DuhamelDeriv.incl_heatH
#print axioms DuhamelDeriv.duh_cocycle
#print axioms DuhamelDeriv.duhνSame_cocycle
#print axioms DuhamelDeriv.scaleG_incl
#print axioms DuhamelDeriv.incl_duh
#print axioms DuhamelDeriv.incl_duhνSame
#print axioms DuhamelDeriv.scaleG_apply_mul
#print axioms DuhamelDeriv.norm_duh_avg_le
#print axioms DuhamelDeriv.duh_avg_sub
#print axioms DuhamelDeriv.tendsto_duh_avg
#print axioms DuhamelDeriv.tendsto_duhνSame_avg
#print axioms DuhamelDeriv.duh_zero
#print axioms DuhamelDeriv.duhνSame_zero
#print axioms DuhamelDeriv.hasDerivWithinAt_Ici_translate
#print axioms DuhamelDeriv.hasDerivWithinAt_duhνSame_Ici
#print axioms DuhamelDeriv.incl_heatUp_to_heatH
#print axioms DuhamelDeriv.incl_duhUp_to_duh
#print axioms DuhamelDeriv.incl_duhν_to_duhνSame
#print axioms DuhamelDeriv.incl_comp
#print axioms DuhamelDeriv.incl_heatH_of_le
#print axioms DuhamelDeriv.incl_duhνSame_of_le

end DuhamelDeriv
