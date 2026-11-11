import Scratch.Nonlinear
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.MetricSpace.Contracting

set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

/-! # Viscosity-scaled Duhamel integral and the Kato mild map on `C([0,T]; Ĥ³)`

`duhν ν G t = ∫₀ᵗ e^{ν(t-s)Δ} G(s) ds` is obtained from `duhUp` by the time change
`σ = ν s`. The mild map `Φ(u)(t) = e^{ν t Δ} u₀ - ∫₀ᵗ e^{ν(t-s)Δ} N(u(s)) ds`
is a contraction on a closed ball of `C([0,T]; Ĥ³)` for small `T > 0`. -/

open MeasureTheory Real Filter Topology Set Metric ContinuousMap
open scoped ENNReal NNReal

noncomputable section
namespace MildExistence

open LerayHeat SobolevFourier SobolevHilbert HeatSobolev Duhamel DuhamelUp
open ProductEstimate ProductH3 Nonlinear

variable {m : ℕ}

/-! ## Viscosity-scaled Duhamel integral -/

/-- Time-rescaled source `Ĝ(σ) = ν⁻¹ • G(σ/ν)`. -/
def scaleG (ν : ℝ) (G : ℝ → Hm m) : ℝ → Hm m := fun σ => ((ν⁻¹ : ℝ) : ℂ) • G (σ / ν)

lemma continuous_scaleG {ν : ℝ} {G : ℝ → Hm m} (hG : Continuous G) :
    Continuous (scaleG ν G) :=
  continuous_const.smul (hG.comp (continuous_id.div_const ν))

lemma norm_scaleG {ν : ℝ} (hν : 0 < ν) (G : ℝ → Hm m) (σ : ℝ) :
    ‖scaleG ν G σ‖ = ν⁻¹ * ‖G (σ / ν)‖ := by
  rw [scaleG, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hν)]

lemma scaleG_sub (ν : ℝ) (G H : ℝ → Hm m) :
    scaleG ν (fun s => G s - H s) = fun σ => scaleG ν G σ - scaleG ν H σ := by
  funext σ; simp only [scaleG, smul_sub]

lemma scaleG_bound {ν M : ℝ} (hν : 0 < ν) {G : ℝ → Hm m} {t : ℝ}
    (hM : ∀ s ∈ Icc 0 t, ‖G s‖ ≤ M) {σ : ℝ} (hσ : σ ∈ Icc 0 (ν * t)) :
    ‖scaleG ν G σ‖ ≤ ν⁻¹ * M := by
  rw [norm_scaleG hν]
  have hs : σ / ν ∈ Icc 0 t := by
    constructor
    · exact div_nonneg hσ.1 hν.le
    · exact (div_le_iff₀ hν).2 (by simpa [mul_comm] using hσ.2)
  exact mul_le_mul_of_nonneg_left (hM _ hs) (inv_nonneg.2 hν.le)

/-- Identity `ν⁻¹ (ν t + 2 √(ν t)) = t + 2 √(t/ν)`. -/
lemma visc_time {ν t : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) :
    ν⁻¹ * (ν * t + 2 * Real.sqrt (ν * t)) = t + 2 * Real.sqrt (t / ν) := by
  have hν0 : ν ≠ 0 := hν.ne'
  have hsqrt : ν⁻¹ * Real.sqrt (ν * t) = Real.sqrt (t / ν) := by
    have hl : 0 ≤ ν⁻¹ * Real.sqrt (ν * t) :=
      mul_nonneg (inv_nonneg.2 hν.le) (Real.sqrt_nonneg _)
    have hr : 0 ≤ Real.sqrt (t / ν) := Real.sqrt_nonneg _
    refine (sq_eq_sq₀ hl hr).mp ?_
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hν.le ht), Real.sq_sqrt (div_nonneg ht hν.le),
      inv_pow]
    field_simp [hν0]
  calc ν⁻¹ * (ν * t + 2 * Real.sqrt (ν * t))
      = ν⁻¹ * (ν * t) + ν⁻¹ * (2 * Real.sqrt (ν * t)) := by rw [mul_add]
    _ = t + 2 * (ν⁻¹ * Real.sqrt (ν * t)) := by
        have h1 : ν⁻¹ * (ν * t) = t := by rw [← mul_assoc, inv_mul_cancel₀ hν0, one_mul]
        have h2 : ν⁻¹ * (2 * Real.sqrt (ν * t)) = 2 * (ν⁻¹ * Real.sqrt (ν * t)) := by ring
        rw [h1, h2]
    _ = t + 2 * Real.sqrt (t / ν) := by rw [hsqrt]

/-- Viscosity-scaled Duhamel integral `∫₀ᵗ e^{ν(t-s)Δ} G(s) ds`. -/
def duhν (m : ℕ) (ν : ℝ) (G : ℝ → Hm m) (t : ℝ) : Hm (m + 1) :=
  duhUp m (scaleG ν G) (ν * t)

lemma duhν_zero {ν : ℝ} (G : ℝ → Hm m) : duhν m ν G 0 = 0 := by
  unfold duhν; rw [mul_zero]; unfold duhUp; exact intervalIntegral.integral_same

/-- **Viscosity-scaled smoothing Duhamel estimate**:
`‖∫₀ᵗ e^{ν(t-s)Δ} G‖_{Ĥ^{m+1}} ≤ M (t + 2 √(t/ν))`. -/
theorem norm_duhν_le {ν : ℝ} (hν : 0 < ν) {G : ℝ → Hm m} (hG : Continuous G) {t M : ℝ}
    (ht : 0 ≤ t) (hM0 : 0 ≤ M) (hM : ∀ s ∈ Icc 0 t, ‖G s‖ ≤ M) :
    ‖duhν m ν G t‖ ≤ M * (t + 2 * Real.sqrt (t / ν)) := by
  have hνt : 0 ≤ ν * t := mul_nonneg hν.le ht
  have hM' : 0 ≤ ν⁻¹ * M := mul_nonneg (inv_nonneg.2 hν.le) hM0
  have hbd : ∀ σ ∈ Icc 0 (ν * t), ‖scaleG ν G σ‖ ≤ ν⁻¹ * M := fun σ hσ => scaleG_bound hν hM hσ
  have := norm_duhUp_le (continuous_scaleG hG) hνt hM' hbd
  unfold duhν
  refine this.trans (le_of_eq ?_)
  calc ν⁻¹ * M * (ν * t + 2 * Real.sqrt (ν * t))
      = M * (ν⁻¹ * (ν * t + 2 * Real.sqrt (ν * t))) := by ring
    _ = M * (t + 2 * Real.sqrt (t / ν)) := by rw [visc_time hν ht]

/-- `duhν` is linear in `G` (difference form). -/
theorem duhν_sub {ν : ℝ} (hν : 0 < ν) {G H : ℝ → Hm m} (hG : Continuous G) (hH : Continuous H)
    {t MG MH : ℝ} (ht : 0 ≤ t) (hMG0 : 0 ≤ MG) (hMG : ∀ s ∈ Icc 0 t, ‖G s‖ ≤ MG)
    (hMH0 : 0 ≤ MH) (hMH : ∀ s ∈ Icc 0 t, ‖H s‖ ≤ MH) :
    duhν m ν G t - duhν m ν H t = duhν m ν (fun s => G s - H s) t := by
  have hνt : 0 ≤ ν * t := mul_nonneg hν.le ht
  unfold duhν
  have e : scaleG ν (fun s => G s - H s) = fun σ => scaleG ν G σ - scaleG ν H σ := scaleG_sub ν G H
  rw [e]
  exact duhUp_sub (continuous_scaleG hG) (continuous_scaleG hH) hνt
    (mul_nonneg (inv_nonneg.2 hν.le) hMG0) (fun σ hσ => scaleG_bound hν hMG hσ)
    (mul_nonneg (inv_nonneg.2 hν.le) hMH0) (fun σ hσ => scaleG_bound hν hMH hσ)

/-- Lipschitz bound: `‖duhν G t - duhν H t‖ ≤ (t + 2√(t/ν)) · sup ‖G-H‖`. -/
theorem norm_duhν_sub_le {ν : ℝ} (hν : 0 < ν) {G H : ℝ → Hm m} (hG : Continuous G)
    (hH : Continuous H) {t MG MH M : ℝ} (ht : 0 ≤ t)
    (hMG0 : 0 ≤ MG) (hMG : ∀ s ∈ Icc 0 t, ‖G s‖ ≤ MG)
    (hMH0 : 0 ≤ MH) (hMH : ∀ s ∈ Icc 0 t, ‖H s‖ ≤ MH)
    (hM0 : 0 ≤ M) (hM : ∀ s ∈ Icc 0 t, ‖G s - H s‖ ≤ M) :
    ‖duhν m ν G t - duhν m ν H t‖ ≤ M * (t + 2 * Real.sqrt (t / ν)) := by
  rw [duhν_sub hν hG hH ht hMG0 hMG hMH0 hMH]
  exact norm_duhν_le hν (hG.sub hH) ht hM0 hM

/-- Continuity in `t` of the viscosity-scaled Duhamel integral on `[0, T]`. -/
theorem continuousOn_duhν {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) {G : ℝ → Hm m} (hG : Continuous G)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ s ∈ Icc 0 T, ‖G s‖ ≤ M) :
    ContinuousOn (duhν m ν G) (Icc 0 T) := by
  have hνT : 0 ≤ ν * T := mul_nonneg hν.le hT
  have hbd : ∀ σ ∈ Icc 0 (ν * T), ‖scaleG ν G σ‖ ≤ ν⁻¹ * M :=
    fun σ hσ => scaleG_bound hν hM hσ
  have hc := continuousOn_duhUp (continuous_scaleG hG)
    (mul_nonneg (inv_nonneg.2 hν.le) hM0) hbd
  have hmaps : MapsTo (fun t : ℝ => ν * t) (Icc 0 T) (Icc 0 (ν * T)) := fun t ht =>
    ⟨mul_nonneg hν.le ht.1, mul_le_mul_of_nonneg_left ht.2 hν.le⟩
  exact hc.comp (continuous_const.mul continuous_id).continuousOn hmaps

lemma heatH_of_nonpos {τ : ℝ} (hτ : τ ≤ 0) (G : Hm m) : heatH m τ G = G := by
  refine Lp.ext ?_
  filter_upwards [coeFn_heatH τ G] with ξ h
  rw [h, gauss_of_nonpos hτ, Complex.ofReal_one, one_smul]

lemma heatH_zero (G : Hm m) : heatH m 0 G = G := heatH_of_nonpos le_rfl G

/-! ## Continuity of `N` along bounded continuous curves -/

lemma continuous_comp_NSN {X : Type*} [TopologicalSpace X] {G : X → Hm 3}
    (hG : Continuous G) {R : ℝ} (hR : ∀ x, ‖G x‖ ≤ R) :
    Continuous (fun x => NSN (G x)) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  have hlip : ∀ y, ‖NSN (G y) - NSN (G x)‖ ≤
      (9 * Cstar * (R + R)) * ‖G y - G x‖ := fun y =>
    (norm_NSN_sub_le (G y) (G x)).trans <|
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add (hR y) (hR x))
          (mul_nonneg (by norm_num) Cstar_nonneg))
        (norm_nonneg _)
  have hc : Continuous fun y => (9 * Cstar * (R + R)) * ‖G y - G x‖ :=
    continuous_const.mul (hG.sub continuous_const).norm
  exact squeeze_zero (fun _ => norm_nonneg _) hlip (by simpa [sub_self, norm_zero, mul_zero] using hc.tendsto x)

lemma norm_extU_le {T : ℝ} (hT : 0 ≤ T) (u : C(Icc (0 : ℝ) T, Hm 3)) (s : ℝ) :
    ‖(ContinuousMap.IccExtend hT u) s‖ ≤ ‖u‖ := by
  change ‖u (projIcc 0 T hT s)‖ ≤ ‖u‖
  exact norm_coe_le_norm u _

lemma continuous_NSN_extU {T : ℝ} (hT : 0 ≤ T) (u : C(Icc (0 : ℝ) T, Hm 3)) :
    Continuous (fun s => NSN ((ContinuousMap.IccExtend hT u) s)) :=
  continuous_comp_NSN (ContinuousMap.IccExtend hT u).continuous (fun s => norm_extU_le hT u s)

lemma Cstar9_nonneg : 0 ≤ 9 * Cstar := mul_nonneg (by norm_num) Cstar_nonneg

lemma norm_NSN_extU_le {T : ℝ} (hT : 0 ≤ T) (u : C(Icc (0 : ℝ) T, Hm 3)) (s : ℝ) :
    ‖NSN ((ContinuousMap.IccExtend hT u) s)‖ ≤ 9 * Cstar * ‖u‖ ^ 2 :=
  (norm_NSN_le _).trans <|
    mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_extU_le hT u s) 2) Cstar9_nonneg

lemma visc_time_mono {ν : ℝ} (hν : 0 < ν) {t T : ℝ} (hT : t ≤ T) (_ht : 0 ≤ t) :
    t + 2 * Real.sqrt (t / ν) ≤ T + 2 * Real.sqrt (T / ν) :=
  add_le_add hT <| mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hT hν.le)) (by norm_num)

/-! ## The mild map on `C([0,T]; Ĥ³)` -/

/-- The path space `C([0,T]; Ĥ³)`. -/
abbrev XT (T : ℝ) := C(Icc (0 : ℝ) T, Hm 3)

/-- Pointwise mild-map formula. -/
def mildFn (ν : ℝ) (u₀ : Hm 3) {T : ℝ} (hT : 0 ≤ T) (u : XT T) (t : ℝ) : Hm 3 :=
  heatH 3 (ν * t) u₀ - duhν 2 ν (fun s => NSN ((ContinuousMap.IccExtend hT u) s)) t

lemma continuousOn_mildFn {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (u₀ : Hm 3) (u : XT T) :
    ContinuousOn (mildFn ν u₀ hT u) (Icc 0 T) :=
  ((continuous_heatH u₀).comp (continuous_const.mul continuous_id)).continuousOn.sub
    (continuousOn_duhν hν hT (continuous_NSN_extU hT u)
      (mul_nonneg Cstar9_nonneg (sq_nonneg _))
      (fun s _ => norm_NSN_extU_le hT u s))

/-- The mild map `Φ(u)(t) = e^{ν t Δ} u₀ - ∫₀ᵗ e^{ν(t-s)Δ} N(u(s)) ds`. -/
def Phi {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (u₀ : Hm 3) (u : XT T) : XT T :=
  ContinuousMap.mk (fun t => mildFn ν u₀ hT u t.1)
    ((continuousOn_mildFn hν hT u₀ u).comp_continuous continuous_subtype_val fun t => t.2)

lemma coe_Phi {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (u₀ : Hm 3) (u : XT T)
    (t : Icc (0 : ℝ) T) : Phi hν hT u₀ u t = mildFn ν u₀ hT u t.1 := rfl

lemma visc_nonneg {ν t : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) :
    0 ≤ t + 2 * Real.sqrt (t / ν) :=
  add_nonneg ht (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))

lemma norm_mildFn_le {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (u₀ : Hm 3) (u : XT T)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖mildFn ν u₀ hT u t‖ ≤
      ‖u₀‖ + (9 * Cstar * ‖u‖ ^ 2) * (T + 2 * Real.sqrt (T / ν)) := by
  unfold mildFn
  refine (norm_sub_le _ _).trans (add_le_add (norm_heatH_le 3 (ν * t) u₀) ?_)
  have hM0 : 0 ≤ 9 * Cstar * ‖u‖ ^ 2 := mul_nonneg Cstar9_nonneg (sq_nonneg _)
  have hbd : ∀ s ∈ Icc 0 t, ‖NSN ((ContinuousMap.IccExtend hT u) s)‖ ≤ 9 * Cstar * ‖u‖ ^ 2 :=
    fun s _ => norm_NSN_extU_le hT u s
  refine (norm_duhν_le hν (continuous_NSN_extU hT u) ht.1 hM0 hbd).trans ?_
  exact mul_le_mul_of_nonneg_left (visc_time_mono hν ht.2 ht.1) hM0

/-- A mild solution on `[0,T]` is a fixed point of `Φ`. -/
def IsMild {T : ℝ} (hT : 0 ≤ T) (ν : ℝ) (u₀ : Hm 3) (u : XT T) : Prop :=
  ∀ t : Icc (0 : ℝ) T,
    u t = heatH 3 (ν * (t : ℝ)) u₀ - duhν 2 ν (fun s => NSN ((ContinuousMap.IccExtend hT u) s)) (t : ℝ)

lemma isMild_iff_fixed {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (u₀ : Hm 3) (u : XT T) :
    IsMild hT ν u₀ u ↔ Phi hν hT u₀ u = u := by
  constructor
  · intro h
    refine ContinuousMap.ext fun t => ?_
    rw [coe_Phi, mildFn]
    exact (h t).symm
  · intro h t
    have ht : u t = Phi hν hT u₀ u t := by rw [h]
    rw [ht, coe_Phi, mildFn]

/-! ## Ball invariance and contraction for small `T` -/

/-- Working radius `R = 2 ‖u₀‖_{Ĥ³} + 1`. -/
def rad (u₀ : Hm 3) : ℝ := 2 * ‖u₀‖ + 1

lemma rad_pos (u₀ : Hm 3) : 0 < rad u₀ := by
  unfold rad; linarith [norm_nonneg u₀]

lemma rad_nonneg (u₀ : Hm 3) : 0 ≤ rad u₀ := (rad_pos u₀).le

lemma le_rad (u₀ : Hm 3) : ‖u₀‖ ≤ rad u₀ := by
  unfold rad; linarith [norm_nonneg u₀]

lemma u0_eq_rad (u₀ : Hm 3) : ‖u₀‖ = (rad u₀ - 1) / 2 := by
  unfold rad; ring

/-- Positive time of length at most `ε` in the viscosity scale `t + 2√(t/ν)`. -/
def timeSlot (ν ε : ℝ) : ℝ := min (ε / 2) (ν * (ε / 4) ^ 2)

lemma timeSlot_pos {ν ε : ℝ} (hν : 0 < ν) (hε : 0 < ε) : 0 < timeSlot ν ε :=
  lt_min (half_pos hε) (mul_pos hν (pow_pos (div_pos hε (by norm_num)) 2))

lemma timeSlot_visc {ν ε T : ℝ} (hν : 0 < ν) (hε : 0 < ε) (_hT0 : 0 ≤ T)
    (hT : T ≤ timeSlot ν ε) : T + 2 * Real.sqrt (T / ν) ≤ ε := by
  have h1 : T ≤ ε / 2 := hT.trans (min_le_left _ _)
  have h2 : T ≤ ν * (ε / 4) ^ 2 := hT.trans (min_le_right _ _)
  have hs : 2 * Real.sqrt (T / ν) ≤ ε / 2 := by
    have hdiv : T / ν ≤ (ε / 4) ^ 2 := (div_le_iff₀ hν).2 (by simpa [mul_comm] using h2)
    have h4 : 0 ≤ ε / 4 := div_nonneg hε.le (by norm_num)
    have hsqrt : Real.sqrt (T / ν) ≤ ε / 4 := (Real.sqrt_le_left h4).2 hdiv
    calc 2 * Real.sqrt (T / ν) ≤ 2 * (ε / 4) :=
        mul_le_mul_of_nonneg_left hsqrt (by norm_num)
      _ = ε / 2 := by ring
  linarith

/-- Duhamel window used for the contraction: `δ = 1 / (2 (18 C⋆ R + 1))`. -/
def delta (u₀ : Hm 3) : ℝ := 1 / (2 * (18 * Cstar * rad u₀ + 1))

lemma Cstar18_rad_nonneg (u₀ : Hm 3) : 0 ≤ 18 * Cstar * rad u₀ :=
  mul_nonneg (mul_nonneg (by norm_num) Cstar_nonneg) (rad_nonneg u₀)

lemma den_pos (u₀ : Hm 3) : 0 < 2 * (18 * Cstar * rad u₀ + 1) :=
  mul_pos (by norm_num) (add_pos_of_nonneg_of_pos (Cstar18_rad_nonneg u₀) one_pos)

lemma delta_pos (u₀ : Hm 3) : 0 < delta u₀ := one_div_pos.2 (den_pos u₀)

/-- Local existence time, depending only on `ν` and `‖u₀‖_{Ĥ³}`. -/
def localTime (ν : ℝ) (u₀ : Hm 3) : ℝ := timeSlot ν (delta u₀)

lemma localTime_pos {ν : ℝ} (hν : 0 < ν) (u₀ : Hm 3) : 0 < localTime ν u₀ :=
  timeSlot_pos hν (delta_pos u₀)

lemma localTime_nonneg {ν : ℝ} (hν : 0 < ν) (u₀ : Hm 3) : 0 ≤ localTime ν u₀ :=
  (localTime_pos hν u₀).le

lemma localTime_visc {ν : ℝ} (hν : 0 < ν) (u₀ : Hm 3) :
    localTime ν u₀ + 2 * Real.sqrt (localTime ν u₀ / ν) ≤ delta u₀ :=
  timeSlot_visc hν (delta_pos u₀) (localTime_nonneg hν u₀) le_rfl

lemma lip_const_le_half (u₀ : Hm 3) :
    18 * Cstar * rad u₀ * delta u₀ ≤ 1 / 2 := by
  unfold delta
  set a := 18 * Cstar * rad u₀
  have ha : 0 ≤ a := Cstar18_rad_nonneg u₀
  have hden : 0 < 2 * (a + 1) := mul_pos (by norm_num) (add_pos_of_nonneg_of_pos ha one_pos)
  change a * (1 / (2 * (a + 1))) ≤ 1 / 2
  rw [mul_one_div]
  refine (div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 2)).2 ?_
  linarith

lemma inv_arith (u₀ : Hm 3) :
    ‖u₀‖ + (9 * Cstar * rad u₀ ^ 2) * delta u₀ ≤ rad u₀ := by
  set R := rad u₀
  have hR0 : 0 ≤ R := rad_nonneg u₀
  rw [u0_eq_rad u₀]
  unfold delta
  have hden : 0 < 2 * (18 * Cstar * R + 1) := den_pos u₀
  rw [mul_one_div]
  have htarget :
      (9 * Cstar * R ^ 2) / (2 * (18 * Cstar * R + 1)) ≤ (R + 1) / 2 := by
    refine (div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 2)).2 ?_
    have : 9 * Cstar * R ^ 2 ≤ (18 * Cstar * R + 1) * (R + 1) := by
      calc 9 * Cstar * R ^ 2
          ≤ 18 * Cstar * R ^ 2 + 18 * Cstar * R + R + 1 := by
            have h1 : 0 ≤ 9 * Cstar * R ^ 2 := mul_nonneg Cstar9_nonneg (sq_nonneg _)
            have h2 : 0 ≤ 18 * Cstar * R := Cstar18_rad_nonneg u₀
            linarith
        _ = (18 * Cstar * R + 1) * (R + 1) := by ring
    linarith
  linarith

lemma mapsTo_Phi {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (u₀ : Hm 3)
    (hTδ : T + 2 * Real.sqrt (T / ν) ≤ delta u₀) :
    MapsTo (Phi hν hT u₀) (closedBall (0 : XT T) (rad u₀))
      (closedBall (0 : XT T) (rad u₀)) := by
  intro u hu
  have hu' : ‖u‖ ≤ rad u₀ := by
    have := mem_closedBall_iff_norm.mp hu
    rwa [sub_zero] at this
  refine mem_closedBall_iff_norm.mpr ?_
  rw [sub_zero]
  refine (ContinuousMap.norm_le (Phi hν hT u₀ u) (rad_nonneg u₀)).2 fun t => ?_
  have eqt : Phi hν hT u₀ u t = mildFn ν u₀ hT u t.1 := coe_Phi hν hT u₀ u t
  rw [eqt]
  have h1 := norm_mildFn_le hν hT u₀ u t.2
  have hquad : 9 * Cstar * ‖u‖ ^ 2 ≤ 9 * Cstar * rad u₀ ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hu' 2) Cstar9_nonneg
  have hstep :
      ‖mildFn ν u₀ hT u t.1‖ ≤
        ‖u₀‖ + (9 * Cstar * rad u₀ ^ 2) * (T + 2 * Real.sqrt (T / ν)) :=
    h1.trans (add_le_add le_rfl (mul_le_mul hquad le_rfl (visc_nonneg hν hT)
      (mul_nonneg Cstar9_nonneg (sq_nonneg _))))
  have hstep' :
      ‖mildFn ν u₀ hT u t.1‖ ≤ ‖u₀‖ + (9 * Cstar * rad u₀ ^ 2) * delta u₀ :=
    hstep.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hTδ (mul_nonneg Cstar9_nonneg (sq_nonneg _))))
  exact hstep'.trans (inv_arith u₀)

lemma extU_sub {T : ℝ} (hT : 0 ≤ T) (u v : XT T) (s : ℝ) :
    ContinuousMap.IccExtend hT (u - v) s = ContinuousMap.IccExtend hT u s - ContinuousMap.IccExtend hT v s := rfl

lemma norm_NSN_extU_sub_le {T : ℝ} (hT : 0 ≤ T) {R : ℝ} (hR : 0 ≤ R)
    {u v : XT T} (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) (s : ℝ) :
    ‖NSN ((ContinuousMap.IccExtend hT u) s) - NSN ((ContinuousMap.IccExtend hT v) s)‖ ≤
      18 * Cstar * R * ‖u - v‖ := by
  have h1 := norm_NSN_sub_le (ContinuousMap.IccExtend hT u s) (ContinuousMap.IccExtend hT v s)
  have hu' : ‖ContinuousMap.IccExtend hT u s‖ ≤ R := (norm_extU_le hT u s).trans hu
  have hv' : ‖ContinuousMap.IccExtend hT v s‖ ≤ R := (norm_extU_le hT v s).trans hv
  have hdiff : ‖ContinuousMap.IccExtend hT u s - ContinuousMap.IccExtend hT v s‖ ≤ ‖u - v‖ := by
    rw [← extU_sub hT u v s]; exact norm_extU_le hT (u - v) s
  have hsum : ‖ContinuousMap.IccExtend hT u s‖ + ‖ContinuousMap.IccExtend hT v s‖ ≤ R + R := add_le_add hu' hv'
  have hC : 0 ≤ 9 * Cstar := Cstar9_nonneg
  refine h1.trans ?_
  have : 9 * Cstar * (‖ContinuousMap.IccExtend hT u s‖ + ‖ContinuousMap.IccExtend hT v s‖) *
      ‖ContinuousMap.IccExtend hT u s - ContinuousMap.IccExtend hT v s‖ ≤
      9 * Cstar * (R + R) * ‖u - v‖ :=
    mul_le_mul (mul_le_mul_of_nonneg_left hsum hC) hdiff
      (norm_nonneg _) (mul_nonneg hC (add_nonneg hR hR))
  refine this.trans (le_of_eq ?_)
  ring

lemma mildFn_sub (ν : ℝ) (u₀ : Hm 3) {T : ℝ} (hT : 0 ≤ T) (u v : XT T) (t : ℝ) :
    mildFn ν u₀ hT u t - mildFn ν u₀ hT v t =
      duhν 2 ν (fun s => NSN ((ContinuousMap.IccExtend hT v) s)) t -
        duhν 2 ν (fun s => NSN ((ContinuousMap.IccExtend hT u) s)) t := by
  simp only [mildFn, sub_sub_sub_cancel_left]

lemma norm_Phi_sub_le {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (u₀ : Hm 3)
    {u v : XT T} (hu : ‖u‖ ≤ rad u₀) (hv : ‖v‖ ≤ rad u₀) (t : Icc (0 : ℝ) T) :
    ‖Phi hν hT u₀ u t - Phi hν hT u₀ v t‖ ≤
      (18 * Cstar * rad u₀ * (T + 2 * Real.sqrt (T / ν))) * ‖u - v‖ := by
  have eu : Phi hν hT u₀ u t = mildFn ν u₀ hT u t.1 := coe_Phi hν hT u₀ u t
  have ev : Phi hν hT u₀ v t = mildFn ν u₀ hT v t.1 := coe_Phi hν hT u₀ v t
  rw [eu, ev, mildFn_sub]
  rw [norm_sub_rev]
  have hR := rad_nonneg u₀
  have hMG0 : 0 ≤ 9 * Cstar * rad u₀ ^ 2 := mul_nonneg Cstar9_nonneg (sq_nonneg _)
  have hMG : ∀ s ∈ Icc 0 T, ‖NSN ((ContinuousMap.IccExtend hT u) s)‖ ≤ 9 * Cstar * rad u₀ ^ 2 :=
    fun s _ => (norm_NSN_extU_le hT u s).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hu 2) Cstar9_nonneg)
  have hMH : ∀ s ∈ Icc 0 T, ‖NSN ((ContinuousMap.IccExtend hT v) s)‖ ≤ 9 * Cstar * rad u₀ ^ 2 :=
    fun s _ => (norm_NSN_extU_le hT v s).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hv 2) Cstar9_nonneg)
  have hM0 : 0 ≤ 18 * Cstar * rad u₀ * ‖u - v‖ :=
    mul_nonneg (Cstar18_rad_nonneg u₀) (norm_nonneg _)
  have hM : ∀ s ∈ Icc 0 t.1, ‖NSN ((ContinuousMap.IccExtend hT u) s) - NSN ((ContinuousMap.IccExtend hT v) s)‖ ≤
      18 * Cstar * rad u₀ * ‖u - v‖ :=
    fun s _ => norm_NSN_extU_sub_le hT hR hu hv s
  have hbd := norm_duhν_sub_le hν (continuous_NSN_extU hT u)
    (continuous_NSN_extU hT v) (t.2.1) hMG0
    (fun s hs => hMG s ⟨hs.1, hs.2.trans t.2.2⟩) hMG0
    (fun s hs => hMH s ⟨hs.1, hs.2.trans t.2.2⟩) hM0 hM
  refine hbd.trans ?_
  have : t.1 + 2 * Real.sqrt (t.1 / ν) ≤ T + 2 * Real.sqrt (T / ν) :=
    visc_time_mono hν t.2.2 t.2.1
  have hK0 : 0 ≤ 18 * Cstar * rad u₀ * ‖u - v‖ := hM0
  calc (18 * Cstar * rad u₀ * ‖u - v‖) * (t.1 + 2 * Real.sqrt (t.1 / ν))
      ≤ (18 * Cstar * rad u₀ * ‖u - v‖) * (T + 2 * Real.sqrt (T / ν)) :=
        mul_le_mul_of_nonneg_left this hK0
    _ = (18 * Cstar * rad u₀ * (T + 2 * Real.sqrt (T / ν))) * ‖u - v‖ := by ring

lemma lipschitz_Phi {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (u₀ : Hm 3)
    (hTδ : T + 2 * Real.sqrt (T / ν) ≤ delta u₀)
    {u v : XT T} (hu : u ∈ closedBall (0 : XT T) (rad u₀))
    (hv : v ∈ closedBall (0 : XT T) (rad u₀)) :
    dist (Phi hν hT u₀ u) (Phi hν hT u₀ v) ≤ (1 / 2) * dist u v := by
  rw [mem_closedBall_iff_norm, sub_zero] at hu hv
  rw [dist_eq_norm, dist_eq_norm]
  have hpt : ∀ t : Icc (0 : ℝ) T,
      ‖(Phi hν hT u₀ u - Phi hν hT u₀ v) t‖ ≤ (1 / 2) * ‖u - v‖ := fun t => by
    have h1 := norm_Phi_sub_le hν hT u₀ hu hv t
    have h2 : 18 * Cstar * rad u₀ * (T + 2 * Real.sqrt (T / ν)) ≤
        18 * Cstar * rad u₀ * delta u₀ :=
      mul_le_mul_of_nonneg_left hTδ (Cstar18_rad_nonneg u₀)
    have h3 : 18 * Cstar * rad u₀ * (T + 2 * Real.sqrt (T / ν)) * ‖u - v‖ ≤
        (18 * Cstar * rad u₀ * delta u₀) * ‖u - v‖ :=
      mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    have h4 : (18 * Cstar * rad u₀ * delta u₀) * ‖u - v‖ ≤ (1 / 2) * ‖u - v‖ :=
      mul_le_mul_of_nonneg_right (lip_const_le_half u₀) (norm_nonneg _)
    exact h1.trans (h3.trans h4)
  exact (norm_le (Phi hν hT u₀ u - Phi hν hT u₀ v)
    (mul_nonneg (by norm_num) (norm_nonneg _))).2 hpt

lemma contracting_Phi {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (u₀ : Hm 3)
    (hTδ : T + 2 * Real.sqrt (T / ν) ≤ delta u₀) :
    ContractingWith (1 / 2 : ℝ≥0)
      ((mapsTo_Phi hν hT u₀ hTδ).restrict (Phi hν hT u₀)
        (closedBall (0 : XT T) (rad u₀)) (closedBall (0 : XT T) (rad u₀))) := by
  refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  simpa [MapsTo.restrict, Subtype.dist_eq] using
    lipschitz_Phi hν hT u₀ hTδ x.2 y.2

lemma const_mem_ball {T : ℝ} (hT : 0 ≤ T) (u₀ : Hm 3) :
    const (Icc (0 : ℝ) T) u₀ ∈ closedBall (0 : XT T) (rad u₀) := by
  rw [mem_closedBall_iff_norm, sub_zero]
  refine (norm_le (const (Icc (0 : ℝ) T) u₀) (rad_nonneg u₀)).2 fun _ => ?_
  simpa using le_rad u₀

/-- Uniqueness of mild solutions inside the working ball. -/
theorem unique_mild_in_ball {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (u₀ : Hm 3)
    (hTδ : T + 2 * Real.sqrt (T / ν) ≤ delta u₀)
    {u v : XT T} (hu : u ∈ closedBall (0 : XT T) (rad u₀))
    (hv : v ∈ closedBall (0 : XT T) (rad u₀))
    (huM : IsMild hT ν u₀ u) (hvM : IsMild hT ν u₀ v) : u = v := by
  have fu : Phi hν hT u₀ u = u := (isMild_iff_fixed hν hT u₀ u).1 huM
  have fv : Phi hν hT u₀ v = v := (isMild_iff_fixed hν hT u₀ v).1 hvM
  have hd := lipschitz_Phi hν hT u₀ hTδ hu hv
  rw [fu, fv] at hd
  have hnn : 0 ≤ dist u v := dist_nonneg
  have : dist u v = 0 := le_antisymm (by nlinarith) hnn
  exact eq_of_dist_eq_zero this

/-- **Local mild existence and uniqueness** on `C([0,T]; Ĥ³)` for `ν > 0` and
`T = localTime ν u₀ > 0`. The unique mild solution in the closed ball of radius
`rad u₀` is obtained as the Banach fixed point of `Φ`. -/
theorem local_mild_existence (ν : ℝ) (hν : 0 < ν) (u₀ : Hm 3) :
    let T := localTime ν u₀
    0 < T ∧
      ∃ u : XT T, u ∈ closedBall (0 : XT T) (rad u₀) ∧
        IsMild (localTime_nonneg hν u₀) ν u₀ u ∧
        ∀ v ∈ closedBall (0 : XT T) (rad u₀),
          IsMild (localTime_nonneg hν u₀) ν u₀ v → v = u := by
  set T := localTime ν u₀
  have hT : 0 ≤ T := localTime_nonneg hν u₀
  have hTδ : T + 2 * Real.sqrt (T / ν) ≤ delta u₀ := localTime_visc hν u₀
  have hsc : IsComplete (closedBall (0 : XT T) (rad u₀)) := isClosed_closedBall.isComplete
  have hsf := mapsTo_Phi hν hT u₀ hTδ
  have hf := contracting_Phi hν hT u₀ hTδ
  have hx : const (Icc (0 : ℝ) T) u₀ ∈ closedBall (0 : XT T) (rad u₀) := const_mem_ball hT u₀
  have he : edist (const (Icc (0 : ℝ) T) u₀)
      (Phi hν hT u₀ (const (Icc (0 : ℝ) T) u₀)) ≠ ⊤ := (edist_lt_top _ _).ne
  obtain ⟨u, hu, hfix, _, _⟩ :=
    hf.exists_fixedPoint' hsc hsf hx he
  refine ⟨localTime_pos hν u₀, u, hu, (isMild_iff_fixed hν hT u₀ u).2 (by exact hfix), ?_⟩
  intro v hv hvM
  exact unique_mild_in_ball hν hT u₀ hTδ hv hu hvM
    ((isMild_iff_fixed hν hT u₀ u).2 (by exact hfix))

#print axioms MildExistence.norm_duhν_le
#print axioms MildExistence.continuousOn_duhν
#print axioms MildExistence.local_mild_existence
#print axioms MildExistence.unique_mild_in_ball

end MildExistence
