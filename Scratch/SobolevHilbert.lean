import Scratch.HeatSobolev

/-! # Fourier-side Sobolev Hilbert spaces `Ĥ^m = L²(sobW m dξ; ℂ³)` and multipliers between them

`Hm m` is the Fourier image of `H^m`: by `SobolevFourier.sobolevEnergy_eq_fourierEnergy`,
`‖𝓕 F‖²_{Hm m} = fourierEnergy m F = sobolevEnergy m f`. Bounded symbols act between the spaces;
in particular the heat multiplier contracts `Hm m` and maps `Hm m → Hm (m+1)` (smoothing). -/

open MeasureTheory FourierTransform Real
open scoped ENNReal

noncomputable section
namespace SobolevHilbert

open LerayHeat SobolevFourier HeatSobolev

lemma measurable_sobW (m : ℕ) : Measurable (sobW m) := by
  unfold sobW
  exact Finset.measurable_sum _ fun k _ =>
    (Finset.measurable_sum _ fun i _ => (measurable_sym i).enorm.pow_const 2).pow_const k

/-- Fourier-side weighted measure `sobW m ξ dξ`. -/
def μw (m : ℕ) : Measure E3 := volume.withDensity (sobW m)

/-- Fourier-side Sobolev space `Ĥ^m := L²(sobW m dξ; ℂ³)`. -/
abbrev Hm (m : ℕ) := Lp (α := E3) V 2 (μw m)

lemma ac_μw (m : ℕ) : μw m ≪ volume := withDensity_absolutelyContinuous _ _

lemma one_le_sobW (m : ℕ) (ξ : E3) : 1 ≤ sobW m ξ := by
  have := Finset.single_le_sum (s := Finset.range (m + 1))
    (f := fun k => (∑ i : Fin 3, ‖sym i ξ‖ₑ ^ 2) ^ k) (fun _ _ => zero_le _)
    (Finset.mem_range.2 (Nat.succ_pos m))
  simpa [sobW] using this

lemma ac_vol (m : ℕ) : volume ≪ μw m :=
  withDensity_absolutelyContinuous' (measurable_sobW m).aemeasurable
    (Filter.Eventually.of_forall fun ξ => (zero_lt_one.trans_le (one_le_sobW m ξ)).ne')

lemma ac_ww (m m' : ℕ) : μw m' ≪ μw m := (ac_μw m').trans (ac_vol m)

lemma eLpNorm_sq (f : E3 → V) (μ : Measure E3) : eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

lemma sobW_lt_top (m : ℕ) (ξ : E3) : sobW m ξ < ⊤ := by
  rw [sobW_eq]; exact ENNReal.ofReal_lt_top

lemma lintegral_μw (m : ℕ) (f : E3 → ℝ≥0∞) :
    ∫⁻ ξ, f ξ ∂(μw m) = ∫⁻ ξ, sobW m ξ * f ξ :=
  lintegral_withDensity_eq_lintegral_mul_non_measurable _ (measurable_sobW m)
    (Filter.Eventually.of_forall (sobW_lt_top m)) f

/-- `fourierEnergy` is the squared `Ĥ^m` norm of the Fourier transform. -/
theorem fourierEnergy_eq_eLpNorm (m : ℕ) (F : L2V) :
    fourierEnergy m F = eLpNorm ((𝓕 F : L2V) : E3 → V) 2 (μw m) ^ 2 := by
  rw [eLpNorm_sq, lintegral_μw m]
  rfl

lemma enorm_pow_ne_top {x : ℝ≥0∞} {K : ℝ≥0∞} (hK : K ≠ ⊤) {y : ℝ≥0∞} (hy : y ≠ ⊤)
    (h : x ^ 2 ≤ K * y ^ 2) : x ≠ ⊤ := by
  rintro rfl
  have : (⊤ : ℝ≥0∞) ≤ K * y ^ 2 := by simpa using h
  exact (ENNReal.mul_lt_top hK.lt_top (ENNReal.pow_lt_top hy.lt_top)).ne (top_le_iff.1 this)

section WMul
variable {m m' : ℕ} (T : E3 → V →L[ℂ] V)
  (hT : ∀ g : E3 → V, AEStronglyMeasurable g → AEStronglyMeasurable (fun ξ => T ξ (g ξ)))
  (K : ℝ) (hK : 0 ≤ K) (hb : ∀ ξ, sobW m' ξ * ‖T ξ‖ₑ ^ 2 ≤ ENNReal.ofReal K * sobW m ξ)

lemma enorm_clm_apply_le (A : V →L[ℂ] V) (v : V) : ‖A v‖ₑ ≤ ‖A‖ₑ * ‖v‖ₑ := by
  simp only [enorm_eq_nnnorm]
  exact_mod_cast A.le_opNNNorm v

include hb in
lemma eLpNorm_sq_wmul_le (G : Hm m) :
    eLpNorm (fun ξ => T ξ (G ξ)) 2 (μw m') ^ 2 ≤ ENNReal.ofReal K * eLpNorm G 2 (μw m) ^ 2 := by
  rw [eLpNorm_sq, eLpNorm_sq, lintegral_μw, lintegral_μw, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun ξ => ?_
  calc sobW m' ξ * ‖T ξ ((G : E3 → V) ξ)‖ₑ ^ 2
      ≤ sobW m' ξ * (‖T ξ‖ₑ ^ 2 * ‖(G : E3 → V) ξ‖ₑ ^ 2) := by
        refine mul_le_mul_right ?_ _
        rw [← mul_pow]; exact pow_le_pow_left₀ (zero_le _) (enorm_clm_apply_le _ _) 2
    _ = (sobW m' ξ * ‖T ξ‖ₑ ^ 2) * ‖(G : E3 → V) ξ‖ₑ ^ 2 := by ring
    _ ≤ (ENNReal.ofReal K * sobW m ξ) * ‖(G : E3 → V) ξ‖ₑ ^ 2 := mul_le_mul_left (hb ξ) _
    _ = _ := by ring

include hT hb in
lemma memLp_wmul (G : Hm m) : MemLp (fun ξ => T ξ (G ξ)) 2 (μw m') := by
  refine ⟨((hT _ (Lp.stronglyMeasurable G).aestronglyMeasurable).mono_ac (ac_μw m')), ?_⟩
  exact (enorm_pow_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top G)
    (eLpNorm_sq_wmul_le T K hb G)).lt_top

/-- Underlying map of the weighted multiplier. -/
def wmulFun (G : Hm m) : Hm m' := (memLp_wmul T hT K hb G).toLp _

lemma coeFn_wmulFun (G : Hm m) :
    (wmulFun T hT K hb G : E3 → V) =ᵐ[μw m'] fun ξ => T ξ (G ξ) :=
  MemLp.coeFn_toLp (memLp_wmul T hT K hb G)

lemma wmulFun_add (G H : Hm m) :
    wmulFun T hT K hb (G + H) = wmulFun T hT K hb G + wmulFun T hT K hb H := by
  refine Lp.ext ?_
  filter_upwards [coeFn_wmulFun T hT K hb (G + H), (ac_ww m m').ae_le (Lp.coeFn_add G H),
    Lp.coeFn_add (wmulFun T hT K hb G) (wmulFun T hT K hb H), coeFn_wmulFun T hT K hb G,
    coeFn_wmulFun T hT K hb H] with ξ h1 h2 h3 h4 h5
  rw [h1, h3, Pi.add_apply, h4, h5, h2, Pi.add_apply, map_add]

lemma wmulFun_smul (c : ℂ) (G : Hm m) : wmulFun T hT K hb (c • G) = c • wmulFun T hT K hb G := by
  refine Lp.ext ?_
  filter_upwards [coeFn_wmulFun T hT K hb (c • G), (ac_ww m m').ae_le (Lp.coeFn_smul c G),
    Lp.coeFn_smul c (wmulFun T hT K hb G), coeFn_wmulFun T hT K hb G] with ξ h1 h2 h3 h4
  rw [h1, h3, Pi.smul_apply, h4, h2, Pi.smul_apply, map_smul]

include hK hb in
lemma norm_wmulFun_le (G : Hm m) : ‖wmulFun T hT K hb G‖ ≤ Real.sqrt K * ‖G‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (coeFn_wmulFun T hT K hb G)]
  have h := eLpNorm_sq_wmul_le T K hb G
  have hx := (memLp_wmul T hT K hb G).eLpNorm_ne_top
  have hy := Lp.eLpNorm_ne_top G
  set x := eLpNorm (fun ξ => T ξ (G ξ)) 2 (μw m')
  set y := eLpNorm G 2 (μw m)
  have h' : x.toReal ^ 2 ≤ K * y.toReal ^ 2 := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hy)) h
    rwa [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hK] at this
  calc x.toReal = Real.sqrt (x.toReal ^ 2) := (Real.sqrt_sq ENNReal.toReal_nonneg).symm
    _ ≤ Real.sqrt (K * y.toReal ^ 2) := Real.sqrt_le_sqrt h'
    _ = Real.sqrt K * y.toReal := by rw [Real.sqrt_mul hK, Real.sqrt_sq ENNReal.toReal_nonneg]

/-- Weighted multiplier `Ĥ^m → Ĥ^{m'}`, `G ↦ (ξ ↦ T ξ (G ξ))`, norm `≤ √K`. -/
def wmul : Hm m →L[ℂ] Hm m' :=
  LinearMap.mkContinuous ⟨⟨wmulFun T hT K hb, wmulFun_add T hT K hb⟩, wmulFun_smul T hT K hb⟩
    (Real.sqrt K) (norm_wmulFun_le T hT K hK hb)

lemma coeFn_wmul (G : Hm m) : (wmul T hT K hK hb G : E3 → V) =ᵐ[μw m'] fun ξ => T ξ (G ξ) :=
  coeFn_wmulFun T hT K hb G

lemma norm_wmul_le (G : Hm m) : ‖wmul T hT K hK hb G‖ ≤ Real.sqrt K * ‖G‖ :=
  norm_wmulFun_le T hT K hK hb G

end WMul

/-! ## Instances: heat (contraction and smoothing), Leray, inclusions -/

lemma enorm_sq_le_of_norm_le {A : V →L[ℂ] V} {r : ℝ} (hr : 0 ≤ r) (h : ‖A‖ ≤ r) :
    ‖A‖ₑ ^ 2 ≤ ENNReal.ofReal (r ^ 2) := by
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) h 2)

lemma norm_heatSym_le_gauss (τ : ℝ) (ξ : E3) : ‖heatSym τ ξ‖ ≤ gauss τ ξ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (gauss_pos τ ξ).le fun v => ?_
  rw [heatSym_apply, norm_smul, Complex.norm_real, Real.norm_of_nonneg (gauss_pos τ ξ).le]

lemma bound_one {m : ℕ} {A : E3 → V →L[ℂ] V} (hA : ∀ ξ, ‖A ξ‖ ≤ 1) (ξ : E3) :
    sobW m ξ * ‖A ξ‖ₑ ^ 2 ≤ ENNReal.ofReal 1 * sobW m ξ := by
  have := enorm_sq_le_of_norm_le zero_le_one (hA ξ)
  rw [one_pow] at this
  rw [mul_comm]; exact mul_le_mul_left this _

/-- `e^{τΔ}` on `Ĥ^m` (contraction). -/
def heatH (m : ℕ) (τ : ℝ) : Hm m →L[ℂ] Hm m :=
  wmul (heatSym τ) (heatSym_meas τ) 1 zero_le_one (bound_one (heatSym_norm τ))

lemma norm_heatH_le (m : ℕ) (τ : ℝ) (G : Hm m) : ‖heatH m τ G‖ ≤ ‖G‖ := by
  simpa using norm_wmul_le (heatSym τ) (heatSym_meas τ) 1 zero_le_one
    (bound_one (m := m) (heatSym_norm τ)) G

lemma bound_up (m : ℕ) {τ : ℝ} (hτ : 0 < τ) (ξ : E3) :
    sobW (m + 1) ξ * ‖heatSym τ ξ‖ₑ ^ 2 ≤ ENNReal.ofReal (1 + 1 / (2 * τ)) * sobW m ξ := by
  have h1 := enorm_sq_le_of_norm_le (gauss_pos τ ξ).le (norm_heatSym_le_gauss τ ξ)
  calc sobW (m + 1) ξ * ‖heatSym τ ξ‖ₑ ^ 2 ≤ sobW (m + 1) ξ * ENNReal.ofReal (gauss τ ξ ^ 2) :=
        mul_le_mul_right h1 _
    _ ≤ ENNReal.ofReal (1 + 1 / (2 * τ)) * sobW m ξ := by
        rw [sobW_eq_Sp, sobW_eq_Sp, ← ENNReal.ofReal_mul (Sp_nonneg _ (by positivity)),
          ← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (Sp_succ_gauss_le m hτ ξ)

/-- **Smoothing** `e^{τΔ} : Ĥ^m → Ĥ^{m+1}` for `τ > 0`, norm `≤ √(1 + 1/(2τ))`. -/
def heatUp (m : ℕ) {τ : ℝ} (hτ : 0 < τ) : Hm m →L[ℂ] Hm (m + 1) :=
  wmul (heatSym τ) (heatSym_meas τ) (1 + 1 / (2 * τ)) (by positivity) (bound_up m hτ)

lemma norm_heatUp_le (m : ℕ) {τ : ℝ} (hτ : 0 < τ) (G : Hm m) :
    ‖heatUp m hτ G‖ ≤ Real.sqrt (1 + 1 / (2 * τ)) * ‖G‖ :=
  norm_wmul_le (heatSym τ) (heatSym_meas τ) _ (by positivity) (bound_up m hτ) G

/-- Leray projector on `Ĥ^m` (contraction). -/
def lerayH (m : ℕ) : Hm m →L[ℂ] Hm m :=
  wmul lerSym lerSym_meas 1 zero_le_one (bound_one lerSym_norm)

lemma norm_lerayH_le (m : ℕ) (G : Hm m) : ‖lerayH m G‖ ≤ ‖G‖ := by
  simpa using norm_wmul_le lerSym lerSym_meas 1 zero_le_one (bound_one (m := m) lerSym_norm) G

lemma sobW_mono {m m' : ℕ} (h : m' ≤ m) (ξ : E3) : sobW m' ξ ≤ sobW m ξ :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun _ _ _ => zero_le _

/-- Inclusion `Ĥ^m ↪ Ĥ^{m'}` for `m' ≤ m` (norm `≤ 1`). -/
def incl {m m' : ℕ} (h : m' ≤ m) : Hm m →L[ℂ] Hm m' :=
  wmul (fun _ => ContinuousLinearMap.id ℂ V) (fun g hg => hg) 1 zero_le_one (fun ξ => by
    calc sobW m' ξ * ‖ContinuousLinearMap.id ℂ V‖ₑ ^ 2 ≤ sobW m' ξ * 1 := by
          refine mul_le_mul_right ?_ _
          have := enorm_sq_le_of_norm_le zero_le_one (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := V))
          simpa using this
      _ ≤ ENNReal.ofReal 1 * sobW m ξ := by simpa using sobW_mono h ξ)

/-! ## From `L²` fields with finite Fourier energy to `Ĥ^m` -/

lemma memLp_fourier_of_energy {m : ℕ} {F : L2V} (h : fourierEnergy m F < ⊤) :
    MemLp ((𝓕 F : L2V) : E3 → V) 2 (μw m) := by
  refine ⟨(Lp.stronglyMeasurable _).aestronglyMeasurable, ?_⟩
  rw [fourierEnergy_eq_eLpNorm] at h
  refine lt_of_le_of_ne le_top fun htop => ?_
  rw [htop] at h
  simp at h

/-- `F ↦ 𝓕F ∈ Ĥ^m` for `fourierEnergy m F < ⊤`. -/
def toHm {m : ℕ} (F : L2V) (h : fourierEnergy m F < ⊤) : Hm m := (memLp_fourier_of_energy h).toLp _

lemma norm_toHm_sq {m : ℕ} (F : L2V) (h : fourierEnergy m F < ⊤) :
    ‖toHm F h‖ ^ 2 = (fourierEnergy m F).toReal := by
  rw [Lp.norm_def, toHm, eLpNorm_congr_ae (MemLp.coeFn_toLp _), fourierEnergy_eq_eLpNorm,
    ENNReal.toReal_pow]

lemma fourierEnergy_heat_lt_top {m : ℕ} (τ : ℝ) {F : L2V} (h : fourierEnergy m F < ⊤) :
    fourierEnergy m (heat τ F) < ⊤ :=
  (HeatSobolev.fourierEnergy_heat_le m τ F).trans_lt h

/-- `e^{τΔ}` on `L²` and on `Ĥ^m` agree. -/
theorem heatH_toHm {m : ℕ} (τ : ℝ) {F : L2V} (h : fourierEnergy m F < ⊤) :
    heatH m τ (toHm F h) = toHm (heat τ F) (fourierEnergy_heat_lt_top τ h) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_wmul (heatSym τ) (heatSym_meas τ) 1 zero_le_one
      (bound_one (m := m) (heatSym_norm τ)) (toHm F h),
    MemLp.coeFn_toLp (memLp_fourier_of_energy h),
    MemLp.coeFn_toLp (memLp_fourier_of_energy (fourierEnergy_heat_lt_top τ h)),
    (ac_μw m).ae_le (coeFn_fourier_heat τ F)] with ξ h1 h2 h3 h4
  change (heatH m τ (toHm F h) : E3 → V) ξ = _ at h1
  rw [h1, show (toHm (heat τ F) _ : E3 → V) ξ = _ from h3, h4,
    show (toHm F h : E3 → V) ξ = _ from h2, heatSym_apply]

end SobolevHilbert

#print axioms SobolevHilbert.fourierEnergy_eq_eLpNorm
#print axioms SobolevHilbert.norm_heatH_le
#print axioms SobolevHilbert.norm_heatUp_le
#print axioms SobolevHilbert.norm_lerayH_le
#print axioms SobolevHilbert.incl
#print axioms SobolevHilbert.norm_toHm_sq
#print axioms SobolevHilbert.heatH_toHm
