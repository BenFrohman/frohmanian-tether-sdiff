import Scratch.SobolevHilbert

/-! # Heat semigroup on `Ĥ^m`: semigroup law, strong continuity; Duhamel integral -/

open MeasureTheory FourierTransform Real Filter Topology
open scoped ENNReal

noncomputable section
namespace Duhamel

open LerayHeat SobolevFourier HeatSobolev SobolevHilbert

variable {m : ℕ}

lemma coeFn_heatH (τ : ℝ) (G : Hm m) :
    (heatH m τ G : E3 → V) =ᵐ[μw m] fun ξ => ((gauss τ ξ : ℝ) : ℂ) • (G : E3 → V) ξ := by
  filter_upwards [coeFn_wmul (heatSym τ) (heatSym_meas τ) 1 zero_le_one
    (bound_one (m := m) (heatSym_norm τ)) G] with ξ h
  exact h

/-- Semigroup law on `Ĥ^m`. -/
theorem heatH_heatH {σ τ : ℝ} (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (G : Hm m) :
    heatH m σ (heatH m τ G) = heatH m (σ + τ) G := by
  refine Lp.ext ?_
  filter_upwards [coeFn_heatH σ (heatH m τ G), coeFn_heatH τ G, coeFn_heatH (σ + τ) G]
    with ξ h1 h2 h3
  rw [h1, h2, h3, smul_smul, ← Complex.ofReal_mul, gauss_mul hσ hτ]

lemma heatH_max (τ : ℝ) (G : Hm m) : heatH m τ G = heatH m (max τ 0) G := by
  have : heatSym τ = heatSym (max τ 0) := by
    funext ξ; simp only [heatSym, gauss, max_eq_left (le_max_right τ 0)]
  simp only [heatH, this]

lemma heatH_sub (τ : ℝ) (G H : Hm m) : heatH m τ (G - H) = heatH m τ G - heatH m τ H :=
  map_sub _ _ _

/-- Strong continuity of `e^{τΔ}` on `Ĥ^m` at `τ = 0`. -/
theorem tendsto_heatH_zero (G : Hm m) : Tendsto (fun τ => heatH m τ G) (𝓝 0) (𝓝 G) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have key : ∀ τ, (⇑(heatH m τ G) - ⇑G) =ᵐ[μw m]
      fun ξ => (((gauss τ ξ - 1 : ℝ)) : ℂ) • (G : E3 → V) ξ := by
    intro τ
    filter_upwards [coeFn_heatH τ G] with ξ h
    rw [Pi.sub_apply, h, Complex.ofReal_sub, sub_smul, Complex.ofReal_one, one_smul]
  have hg : Measurable (G : E3 → V) := (Lp.stronglyMeasurable G).measurable
  have hlim : Tendsto (fun τ => ∫⁻ ξ, ‖(((gauss τ ξ - 1 : ℝ)) : ℂ) • (G : E3 → V) ξ‖ₑ ^
      ((2 : ENNReal).toReal) ∂(μw m)) (𝓝 0) (𝓝 0) := by
    have := MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence (μ := μw m)
      (l := 𝓝 (0 : ℝ)) (f := fun _ => 0)
      (F := fun τ ξ => ‖(((gauss τ ξ - 1 : ℝ)) : ℂ) • (G : E3 → V) ξ‖ₑ ^ ((2 : ENNReal).toReal))
      (fun ξ => ‖(G : E3 → V) ξ‖ₑ ^ ((2 : ENNReal).toReal))
      (Eventually.of_forall fun τ => by
        have hc : Continuous fun ξ => (((gauss τ ξ - 1 : ℝ)) : ℂ) :=
          Complex.continuous_ofReal.comp ((continuous_gauss τ).sub continuous_const)
        exact ((hc.measurable.smul hg).enorm).pow_const _)
      (Eventually.of_forall fun τ => Eventually.of_forall fun ξ => by
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        rw [enorm_smul]
        refine mul_le_of_le_one_left' ?_
        rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_le_one, Complex.norm_real, Real.norm_eq_abs,
          abs_le]
        constructor <;> linarith [gauss_pos τ ξ, gauss_le_one τ ξ])
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
        (Lp.eLpNorm_lt_top G)).ne
      (Eventually.of_forall fun ξ => by
        have hc : Continuous fun τ => ‖(((gauss τ ξ - 1 : ℝ)) : ℂ) • (G : E3 → V) ξ‖ₑ ^
            ((2 : ENNReal).toReal) := by
          refine ENNReal.continuous_rpow_const.comp (continuous_enorm.comp ?_)
          refine Continuous.smul (Complex.continuous_ofReal.comp ?_) continuous_const
          unfold gauss; fun_prop
        have h0 := hc.tendsto 0
        simpa [gauss_of_nonpos le_rfl] using h0)
    simpa using this
  have h2 := (ENNReal.continuous_rpow_const (y := 1 / (2 : ENNReal).toReal)).tendsto 0 |>.comp hlim
  have h3 : (0 : ENNReal) ^ (1 / (2 : ENNReal).toReal) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
  rw [h3] at h2
  refine h2.congr fun τ => ?_
  simp only [Function.comp_apply]
  rw [eLpNorm_congr_ae (key τ),
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]

lemma norm_heatH_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (G : Hm m) :
    ‖heatH m a G - heatH m b G‖ ≤ ‖heatH m |a - b| G - G‖ := by
  rcases le_total b a with h | h
  · have e : heatH m a G = heatH m b (heatH m (a - b) G) := by
      rw [heatH_heatH hb (sub_nonneg.2 h)]; congr 1; ring
    rw [e, ← heatH_sub, abs_of_nonneg (sub_nonneg.2 h)]
    exact norm_heatH_le _ _ _
  · have e : heatH m b G = heatH m a (heatH m (b - a) G) := by
      rw [heatH_heatH ha (sub_nonneg.2 h)]; congr 1; ring
    rw [e, norm_sub_rev, ← heatH_sub, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)]
    exact norm_heatH_le _ _ _

/-- **Strong continuity** of `τ ↦ e^{τΔ} G` in `Ĥ^m`. -/
theorem continuous_heatH (G : Hm m) : Continuous (fun τ => heatH m τ G) := by
  rw [continuous_iff_continuousAt]
  intro t
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hh : Tendsto (fun s => |max s 0 - max t 0|) (𝓝 t) (𝓝 0) := by
    have : Continuous fun s : ℝ => |max s 0 - max t 0| := by fun_prop
    simpa using this.tendsto t
  have hT := (tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_heatH_zero G)).comp hh
  refine squeeze_zero (fun _ => norm_nonneg _) (fun s => ?_) hT
  rw [heatH_max s, heatH_max t]
  exact norm_heatH_sub_le (le_max_right _ _) (le_max_right _ _) G

/-- Joint continuity of `(τ, G) ↦ e^{τΔ} G`. -/
theorem continuous_heatH_comp {X : Type*} [TopologicalSpace X] {τ : X → ℝ} {G : X → Hm m}
    (hτ : Continuous τ) (hG : Continuous G) : Continuous fun x => heatH m (τ x) (G x) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun y => ‖heatH m (τ y) (G x) - heatH m (τ x) (G x)‖) (𝓝 x) (𝓝 0) := by
    have := ((continuous_heatH (G x)).comp hτ).tendsto x
    exact tendsto_iff_norm_sub_tendsto_zero.1 this
  have h2 : Tendsto (fun y => ‖G y - G x‖) (𝓝 x) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 (hG.tendsto x)
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine squeeze_zero (fun _ => norm_nonneg _) (fun y => ?_) h3
  calc ‖heatH m (τ y) (G y) - heatH m (τ x) (G x)‖
      = ‖heatH m (τ y) (G y - G x) + (heatH m (τ y) (G x) - heatH m (τ x) (G x))‖ := by
        rw [heatH_sub]; congr 1; abel
    _ ≤ ‖heatH m (τ y) (G y - G x)‖ + ‖heatH m (τ y) (G x) - heatH m (τ x) (G x)‖ :=
        norm_add_le _ _
    _ ≤ ‖G y - G x‖ + ‖heatH m (τ y) (G x) - heatH m (τ x) (G x)‖ :=
        add_le_add_left (norm_heatH_le _ _ _) _
    _ = _ := add_comm _ _

/-! ## Duhamel integral `∫₀ᵗ e^{(t-s)Δ} G(s) ds` in `Ĥ^m` -/

/-- Duhamel integral. -/
def duh (m : ℕ) (G : ℝ → Hm m) (t : ℝ) : Hm m := ∫ s in (0 : ℝ)..t, heatH m (t - s) (G s)

lemma continuous_duh_integrand {G : ℝ → Hm m} (hG : Continuous G) (t : ℝ) :
    Continuous fun s => heatH m (t - s) (G s) :=
  continuous_heatH_comp (continuous_const.sub continuous_id) hG

/-- `‖∫₀ᵗ e^{(t-s)Δ}G(s) ds‖ ≤ ∫₀ᵗ ‖G(s)‖ ds`. -/
theorem norm_duh_le {G : ℝ → Hm m} (hG : Continuous G) {t : ℝ} (ht : 0 ≤ t) :
    ‖duh m G t‖ ≤ ∫ s in (0 : ℝ)..t, ‖G s‖ := by
  unfold duh
  refine (intervalIntegral.norm_integral_le_integral_norm ht).trans ?_
  refine intervalIntegral.integral_mono_on ht
    ((continuous_duh_integrand hG t).norm.intervalIntegrable _ _)
    (hG.norm.intervalIntegrable _ _) fun s _ => norm_heatH_le _ _ _

/-- Linearity: `duh G - duh H = duh (G - H)`. -/
theorem duh_sub {G H : ℝ → Hm m} (hG : Continuous G) (hH : Continuous H) (t : ℝ) :
    duh m G t - duh m H t = duh m (fun s => G s - H s) t := by
  unfold duh
  rw [← intervalIntegral.integral_sub ((continuous_duh_integrand hG t).intervalIntegrable _ _)
    ((continuous_duh_integrand hH t).intervalIntegrable _ _)]
  simp only [heatH_sub]

/-- Lipschitz bound for the Duhamel map: `‖duh G t - duh H t‖ ≤ t · sup_{[0,t]} ‖G - H‖`. -/
theorem norm_duh_sub_le {G H : ℝ → Hm m} (hG : Continuous G) (hH : Continuous H) {t : ℝ}
    (ht : 0 ≤ t) {M : ℝ} (hM : ∀ s ∈ Set.Icc 0 t, ‖G s - H s‖ ≤ M) :
    ‖duh m G t - duh m H t‖ ≤ t * M := by
  rw [duh_sub hG hH]
  refine (norm_duh_le (hG.sub hH) ht).trans ?_
  have := intervalIntegral.integral_mono_on (f := fun s => ‖G s - H s‖) (g := fun _ => M) ht
    ((hG.sub hH).norm.intervalIntegrable _ _) (intervalIntegrable_const (μ := volume)) (fun s hs => hM s hs)
  simpa [mul_comm] using this

end Duhamel

#print axioms Duhamel.heatH_heatH
#print axioms Duhamel.tendsto_heatH_zero
#print axioms Duhamel.continuous_heatH
#print axioms Duhamel.continuous_heatH_comp
#print axioms Duhamel.norm_duh_le
#print axioms Duhamel.duh_sub
#print axioms Duhamel.norm_duh_sub_le
