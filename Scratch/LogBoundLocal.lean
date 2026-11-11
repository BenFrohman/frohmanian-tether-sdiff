import Scratch.LogBound
import Scratch.GradBound
import Scratch.SobolevBridge
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Localized BKM log bound: from Schwartz fields to smooth finite-`H³` fields -/

open MeasureTheory SchwartzMap FourierTransform Real FourierCutoff FourierEmb
open scoped ENNReal Laplacian ContDiff

noncomputable section
namespace LogBoundLocal

/-- Leibniz `L²` bound for `φ f - Δ(φ f)` with explicit bounds on `D^i φ`, `i ≤ 2`. -/
theorem leibniz_L2 {φ f : E3 → ℝ} (hφ : ContDiff ℝ ∞ φ) (hf : ContDiff ℝ ∞ f) (B : ℕ → ℝ)
    (hφB : ∀ i y, ‖iteratedFDeriv ℝ i φ y‖ ≤ B i) (G : 𝓢(E3, ℂ))
    (hGdef : ⇑G = fun y => ((φ y * f y : ℝ) : ℂ)) :
    ∫⁻ y, ‖(G - Laplacian.laplacian G) y‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal (27 * (4 * B 0 + 6 * B 1 + 3 * B 2) ^ 2) * energyR 2 f := by
  have hB0 : ∀ i, 0 ≤ B i := fun i => (norm_nonneg _).trans (hφB i 0)
  set K : ℝ := 4 * B 0 + 6 * B 1 + 3 * B 2
  have hK : 0 ≤ K := by have := hB0 0; have := hB0 1; have := hB0 2; positivity
  set q : E3 → ℝ := fun y => φ y * f y
  have hq : ContDiff ℝ ∞ q := hφ.mul hf
  set g : E3 → ℂ := fun y => (q y : ℂ)
  -- iterated derivatives of `g` have the norms of those of `q`
  have hgq : ∀ (i : ℕ) y, ‖iteratedFDeriv ℝ i g y‖ = ‖iteratedFDeriv ℝ i q y‖ := fun i y => by
    have := Complex.ofRealLI.norm_iteratedFDeriv_comp_left (hq.contDiffAt (x := y))
      (i := i) (by exact_mod_cast le_top)
    exact this
  -- Leibniz
  have hleib : ∀ (n : ℕ) y, ‖iteratedFDeriv ℝ n q y‖ ≤ ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i φ y‖ * ‖iteratedFDeriv ℝ (n - i) f y‖ :=
    fun n y => norm_iteratedFDeriv_mul_le hφ hf y (by exact_mod_cast le_top)
  set S : E3 → ℝ := fun y =>
    ∑ k ∈ Finset.range 3, ∑ α : Fin k → Fin 3, ‖iteratedFDeriv ℝ k f y (U α)‖
  have hpt : ∀ y, ‖(G - Laplacian.laplacian G) y‖ ≤ K * S y := by
    intro y
    have hS0 := norm_iter_le f 0 y
    have hS1 := norm_iter_le f 1 y
    have hS2 := norm_iter_le f 2 y
    have hSdef : S y = (∑ α : Fin 0 → Fin 3, ‖iteratedFDeriv ℝ 0 f y (U α)‖) +
        (∑ α : Fin 1 → Fin 3, ‖iteratedFDeriv ℝ 1 f y (U α)‖) +
        (∑ α : Fin 2 → Fin 3, ‖iteratedFDeriv ℝ 2 f y (U α)‖) := by
      simp [S, Finset.sum_range_succ]
    have hG : (G - Laplacian.laplacian G) y = g y - Laplacian.laplacian g y := by
      rw [SchwartzMap.sub_apply, laplacian_apply, hGdef]
    have h0 : ‖g y‖ = ‖iteratedFDeriv ℝ 0 q y‖ := by
      rw [← hgq 0 y, norm_iteratedFDeriv_zero]
    have hL := norm_laplacian_le g y
    rw [hgq 2 y] at hL
    have b0 := hφB 0 y; have b1 := hφB 1 y; have b2 := hφB 2 y
    have n0 := norm_nonneg (iteratedFDeriv ℝ 0 f y)
    have n1 := norm_nonneg (iteratedFDeriv ℝ 1 f y)
    have n2 := norm_nonneg (iteratedFDeriv ℝ 2 f y)
    have t0 : ‖iteratedFDeriv ℝ 0 q y‖ ≤ B 0 * ‖iteratedFDeriv ℝ 0 f y‖ := by
      have := hleib 0 y
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_self,
        Nat.cast_one, one_mul] at this
      exact this.trans (mul_le_mul_of_nonneg_right b0 n0)
    have t2 : ‖iteratedFDeriv ℝ 2 q y‖ ≤ B 0 * ‖iteratedFDeriv ℝ 2 f y‖ +
        2 * B 1 * ‖iteratedFDeriv ℝ 1 f y‖ + B 2 * ‖iteratedFDeriv ℝ 0 f y‖ := by
      have := hleib 2 y
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        show (2 : ℕ) - 0 = 2 from rfl, show (2 : ℕ) - 1 = 1 from rfl,
        show (2 : ℕ) - 2 = 0 from rfl, show Nat.choose 2 0 = 1 from rfl,
        show Nat.choose 2 1 = 2 from rfl, show Nat.choose 2 2 = 1 from rfl, Nat.cast_one,
        Nat.cast_ofNat, one_mul] at this
      nlinarith [mul_le_mul_of_nonneg_right b0 n2, mul_le_mul_of_nonneg_right b1 n1,
        mul_le_mul_of_nonneg_right b2 n0]
    set A0 := ∑ α : Fin 0 → Fin 3, ‖iteratedFDeriv ℝ 0 f y (U α)‖
    set A1 := ∑ α : Fin 1 → Fin 3, ‖iteratedFDeriv ℝ 1 f y (U α)‖
    set A2 := ∑ α : Fin 2 → Fin 3, ‖iteratedFDeriv ℝ 2 f y (U α)‖
    have hA0 : 0 ≤ A0 := n0.trans hS0
    have hA1 : 0 ≤ A1 := n1.trans hS1
    have hA2 : 0 ≤ A2 := n2.trans hS2
    have e0 := hB0 0; have e1 := hB0 1; have e2 := hB0 2
    rw [hG]
    refine (norm_sub_le _ _).trans ?_
    rw [h0, hSdef]
    have u0 := mul_le_mul_of_nonneg_left hS0 e0
    have u1 := mul_le_mul_of_nonneg_left hS1 e1
    have u2 := mul_le_mul_of_nonneg_left hS2 e0
    have u3 := mul_le_mul_of_nonneg_left hS0 e2
    have p1 := mul_nonneg e0 hA1; have p2 := mul_nonneg e0 hA2; have p3 := mul_nonneg e1 hA0
    have p4 := mul_nonneg e1 hA2; have p5 := mul_nonneg e2 hA1; have p6 := mul_nonneg e2 hA2
    have p7 := mul_nonneg e0 hA0; have p8 := mul_nonneg e1 hA1; have p9 := mul_nonneg e2 hA0
    simp only [K]
    nlinarith
  -- L² bound
  show _ ≤ ENNReal.ofReal (27 * K ^ 2) * energyR 2 f
  have hcont : ∀ (k : ℕ) (α : Fin k → Fin 3),
      Continuous fun y => iteratedFDeriv ℝ k f y (U α) := fun k α =>
    (continuous_eval_const (U α)).comp
      (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top))
  have hmeas : ∀ (k : ℕ) (α : Fin k → Fin 3),
      Measurable fun y => ‖iteratedFDeriv ℝ k f y (U α)‖ₑ ^ 2 := fun k α =>
    ((hcont k α).measurable.enorm).pow_const 2
  have hpt2 : ∀ y, ‖(G - Laplacian.laplacian G) y‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (27 * K ^ 2) *
      ∑ k ∈ Finset.range 3, ∑ α : Fin k → Fin 3, ‖iteratedFDeriv ℝ k f y (U α)‖ₑ ^ 2 := by
    intro y
    rw [enorm_rpow_two]
    have hsq : ‖(G - Laplacian.laplacian G) y‖ ^ 2 ≤ 27 * K ^ 2 *
        ∑ k ∈ Finset.range 3, ∑ α : Fin k → Fin 3, ‖iteratedFDeriv ℝ k f y (U α)‖ ^ 2 := by
      have h1 := pow_le_pow_left₀ (norm_nonneg _) (hpt y) 2
      have h2 := sq_le_energy_pt f y
      calc _ ≤ (K * S y) ^ 2 := h1
        _ = K ^ 2 * (S y) ^ 2 := by ring
        _ ≤ K ^ 2 * (27 * ∑ k ∈ Finset.range 3, ∑ α : Fin k → Fin 3,
              ‖iteratedFDeriv ℝ k f y (U α)‖ ^ 2) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = _ := by ring
    refine (ENNReal.ofReal_le_ofReal hsq).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg
      (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  calc ∫⁻ y, ‖(G - Laplacian.laplacian G) y‖ₑ ^ (2 : ℝ)
      ≤ ∫⁻ y, ENNReal.ofReal (27 * K ^ 2) *
        ∑ k ∈ Finset.range 3, ∑ α : Fin k → Fin 3, ‖iteratedFDeriv ℝ k f y (U α)‖ₑ ^ 2 :=
        lintegral_mono hpt2
    _ = ENNReal.ofReal (27 * K ^ 2) * energyR 2 f := by
        rw [lintegral_const_mul _ (Finset.measurable_sum _ fun k _ =>
          Finset.measurable_sum _ fun α _ => hmeas k α)]
        congr 1
        rw [energyR, lintegral_finset_sum _ fun k _ =>
          Finset.measurable_sum _ fun α _ => hmeas k α]
        refine Finset.sum_congr rfl fun k _ => ?_
        exact lintegral_finset_sum _ fun α _ => hmeas k α


/-! ## Component bookkeeping for vector fields `ℝ³ → ℝ³` -/

lemma comp_fderiv {f : E3 → E3} {y : E3} (hf : DifferentiableAt ℝ f y) (a : Fin 3) (v : E3) :
    fderiv ℝ (fun z => f z a) y v = fderiv ℝ f y v a := by
  have : (fun z => f z a) = (EuclideanSpace.proj a : E3 →L[ℝ] ℝ) ∘ f := rfl
  rw [this, fderiv_comp y (EuclideanSpace.proj a).differentiableAt hf,
    ContinuousLinearMap.fderiv]
  rfl

lemma abs_dc_le {f : E3 → E3} {y : E3} (hf : DifferentiableAt ℝ f y) (a b : Fin 3) :
    |fderiv ℝ (fun z => f z a) y (EuclideanSpace.single b 1)| ≤ ‖fderiv ℝ f y‖ := by
  rw [comp_fderiv hf, ← Real.norm_eq_abs]
  refine (PiLp.norm_apply_le _ _).trans ?_
  refine ((fderiv ℝ f y).le_opNorm _).trans (le_of_eq ?_)
  rw [PiLp.norm_single, norm_one, mul_one]

open NavierStokes3D in
/-- Every antisymmetric pair `∂_m f_l - ∂_l f_m` is (up to sign) a component of `curl f`. -/
lemma abs_curl_pair_le (f : E3 → E3) (y : E3) (m l : Fin 3) :
    |fderiv ℝ (fun z => f z l) y (EuclideanSpace.single m 1) -
      fderiv ℝ (fun z => f z m) y (EuclideanSpace.single l 1)| ≤ ‖vorticity f y‖ := by
  have hc : ∀ i, |vorticity f y i| ≤ ‖vorticity f y‖ := fun i => by
    rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le _ _
  have h0 := hc 0; have h1 := hc 1; have h2 := hc 2
  simp only [vorticity, curl, directionalCoord, PiLp.add_apply, PiLp.single_apply] at h0 h1 h2
  fin_cases m <;> fin_cases l <;> simp at h0 h1 h2 ⊢ <;>
    first | positivity | (rw [abs_sub_comm]; assumption) | assumption


lemma l2_le_energy (f : E3 → E3) : ∫⁻ x, ‖f x‖ₑ ^ 2 ≤ R3BKM.sobolevEnergy 3 f := by
  unfold R3BKM.sobolevEnergy
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun k => ∑ α : Fin k → Fin 3,
    ∫⁻ x, ‖iteratedFDeriv ℝ k f x (fun j => EuclideanSpace.single (α j) (1 : ℝ))‖ₑ ^ 2)
    (fun _ _ => zero_le _) (Finset.mem_range.2 (by norm_num : 0 < 3 + 1)))
  simp

lemma energyR_comp_le {f : E3 → E3} (hf : ContDiff ℝ ∞ f) (l : Fin 3) :
    energyR 2 (fun y => f y l) ≤ R3BKM.sobolevEnergy 3 f := by
  have hpt : ∀ (m : ℕ) (α : Fin m → Fin 3) (y : E3),
      ‖iteratedFDeriv ℝ m (fun y => f y l) y (U α)‖ₑ ≤ ‖iteratedFDeriv ℝ m f y (U α)‖ₑ := by
    intro m α y
    have hc := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) l).iteratedFDeriv_comp_left
      (hf.contDiffAt (x := y)) (i := m) (by exact_mod_cast le_top)
    have h2 : (fun y => f y l) = (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) l) ∘ f := rfl
    rw [h2, hc]
    simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
    exact PiLp.enorm_apply_le _ _
  unfold energyR R3BKM.sobolevEnergy
  calc _ ≤ ∑ k ∈ Finset.range 3, ∑ α : Fin k → Fin 3,
        ∫⁻ x, ‖iteratedFDeriv ℝ k f x (fun j => EuclideanSpace.single (α j) (1 : ℝ))‖ₑ ^ 2 :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun α _ =>
          lintegral_mono fun x => by gcongr; exact hpt k α x
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by norm_num : 3 ≤ 3 + 1))
        fun _ _ _ => zero_le _


/-! ## Scaled, translated bump `φ_L(y) = ρ((y - x₀)/L)` -/

lemma exists_bump_bounds : ∃ B : ℕ → ℝ, ∀ i y,
    ‖iteratedFDeriv ℝ i (fun ξ : E3 => LogBound.ρ ξ) y‖ ≤ B i := by
  have hb : ∀ i : ℕ, ∃ B : ℝ, ∀ y, ‖iteratedFDeriv ℝ i (fun ξ : E3 => LogBound.ρ ξ) y‖ ≤ B :=
    fun i => by
    obtain ⟨B, hB⟩ := ((LogBound.ρ.contDiff (n := ⊤)).continuous_iteratedFDeriv
      (by exact_mod_cast le_top)).norm.bddAbove_range_of_hasCompactSupport
      (LogBound.ρ.hasCompactSupport.iteratedFDeriv i).norm
    exact ⟨B, fun y => hB ⟨y, rfl⟩⟩
  choose B hB using hb
  exact ⟨B, hB⟩

/-- `φ_L(y) = ρ(L⁻¹ (y - x₀))`. -/
def φL (x₀ : E3) (L : ℝ) (y : E3) : ℝ := LogBound.ρ (L⁻¹ • (y - x₀))

lemma contDiff_φL (x₀ : E3) (L : ℝ) : ContDiff ℝ ∞ (φL x₀ L) :=
  LogBound.contDiff_ρ.comp ((contDiff_const_smul _).comp (contDiff_id.sub contDiff_const))

lemma norm_iter_φL_le {B : ℕ → ℝ}
    (hB : ∀ i y, ‖iteratedFDeriv ℝ i (fun ξ : E3 => LogBound.ρ ξ) y‖ ≤ B i)
    (x₀ : E3) {L : ℝ} (hL : 0 < L) (i : ℕ) (y : E3) :
    ‖iteratedFDeriv ℝ i (φL x₀ L) y‖ ≤ B i * (L⁻¹) ^ i := by
  set A : E3 →L[ℝ] E3 := L⁻¹ • ContinuousLinearMap.id ℝ E3
  have hA : ‖A‖ ≤ L⁻¹ := by
    refine (norm_smul_le (L⁻¹) (ContinuousLinearMap.id ℝ E3)).trans ?_
    rw [Real.norm_of_nonneg (inv_pos.2 hL).le]
    exact mul_le_of_le_one_right (inv_pos.2 hL).le ContinuousLinearMap.norm_id_le
  have h1 : φL x₀ L = fun y => ((fun ξ : E3 => LogBound.ρ ξ) ∘ A) (y - x₀) := by
    funext y; simp [φL, A]
  rw [h1, iteratedFDeriv_comp_sub, A.iteratedFDeriv_comp_right (LogBound.contDiff_ρ) _
    (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul (hB i _) (pow_le_pow_left₀ (norm_nonneg _) hA i) (by positivity)
    ((norm_nonneg _).trans (hB i 0))

lemma φL_eq_one (x₀ : E3) {L : ℝ} (hL : 0 < L) {y : E3} (hy : ‖y - x₀‖ ≤ L) : φL x₀ L y = 1 := by
  unfold φL
  refine LogBound.ρ_eq_one ?_
  rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 hL).le]
  exact (inv_mul_le_one₀ hL).2 hy

lemma φL_nonneg (x₀ : E3) (L : ℝ) (y : E3) : 0 ≤ φL x₀ L y := LogBound.ρ.nonneg
lemma φL_le_one (x₀ : E3) (L : ℝ) (y : E3) : φL x₀ L y ≤ 1 := LogBound.ρ.le_one

lemma hasCompactSupport_φL (x₀ : E3) {L : ℝ} (hL : 0 < L) : HasCompactSupport (φL x₀ L) := by
  refine HasCompactSupport.intro (isCompact_closedBall x₀ (2 * L)) fun y hy => ?_
  have : 2 * L < ‖y - x₀‖ := by simpa [dist_eq_norm] using hy
  unfold φL
  refine LogBound.ρ_eq_zero ?_
  rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 hL).le, le_inv_mul_iff₀ hL]
  linarith

lemma φL_eventually_one (x₀ : E3) {L : ℝ} (hL : 0 < L) :
    φL x₀ L =ᶠ[nhds x₀] fun _ => 1 := by
  have : Metric.ball x₀ L ∈ nhds x₀ := Metric.ball_mem_nhds x₀ hL
  filter_upwards [this] with y hy
  exact φL_eq_one x₀ hL (by rw [Metric.mem_ball, dist_eq_norm] at hy; exact hy.le)

/-- Directional derivative of a smooth scalar function: bounds on its iterated derivatives. -/
lemma norm_iter_dir_le {φ : E3 → ℝ} (hφ : ContDiff ℝ ∞ φ) (v : E3) (i : ℕ) (y : E3) :
    ‖iteratedFDeriv ℝ i (fun y => fderiv ℝ φ y v) y‖ ≤
      ‖v‖ * ‖iteratedFDeriv ℝ (i + 1) φ y‖ := by
  have h1 : (fun y => fderiv ℝ φ y v) =
      (ContinuousLinearMap.apply ℝ ℝ v) ∘ (fderiv ℝ φ) := rfl
  rw [h1, ← norm_iteratedFDeriv_fderiv]
  refine ((ContinuousLinearMap.apply ℝ ℝ v).norm_iteratedFDeriv_comp_left
    ((hφ.fderiv_right (m := ∞) le_rfl).contDiffAt) (by exact_mod_cast le_top)).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) fun T => by
    rw [ContinuousLinearMap.apply_apply, mul_comm]; exact T.le_opNorm v


/-! ## The localized Schwartz field `G_m = φ_L · f_m` -/

open LineDeriv

section Localize
variable {f : E3 → E3} (hf : ContDiff ℝ ∞ f) (x₀ : E3) {L : ℝ} (hL : 0 < L)

include hf in
lemma contDiff_comp (m : Fin 3) : ContDiff ℝ ∞ (fun y => f y m) :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) m).contDiff.comp hf

/-- Smooth compactly supported real function → complex Schwartz function. -/
def toS {q : E3 → ℝ} (hq : ContDiff ℝ ∞ q) (hs : HasCompactSupport q) : 𝓢(E3, ℂ) :=
  (hs.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hq)

lemma toS_apply {q : E3 → ℝ} (hq : ContDiff ℝ ∞ q) (hs : HasCompactSupport q) (y : E3) :
    toS hq hs y = (q y : ℂ) := rfl

lemma lineDeriv_toS {q : E3 → ℝ} (hq : ContDiff ℝ ∞ q) (hs : HasCompactSupport q) (v y : E3) :
    (∂_{v} (toS hq hs)) y = (fderiv ℝ q y v : ℂ) := by
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have h1 : (⇑(toS hq hs)) = Complex.ofRealCLM ∘ q := rfl
  rw [h1, fderiv_comp y Complex.ofRealCLM.differentiableAt
    ((hq.differentiable (by simp)) y), ContinuousLinearMap.fderiv]
  rfl

include hf in
lemma contDiff_q (m : Fin 3) : ContDiff ℝ ∞ (fun y => φL x₀ L y * f y m) :=
  (contDiff_φL x₀ L).mul (contDiff_comp hf m)

include hL in
lemma hasCompactSupport_q (m : Fin 3) : HasCompactSupport (fun y => φL x₀ L y * f y m) :=
  (hasCompactSupport_φL x₀ hL).mul_right

/-- Localized component `G_m = φ_L f_m` as a complex Schwartz function. -/
def Gs (m : Fin 3) : 𝓢(E3, ℂ) := toS (contDiff_q hf x₀ m) (hasCompactSupport_q x₀ hL m)

/-- `∂_a φ_L` and `∂_a f_m`. -/
def dφ (x₀ : E3) (L : ℝ) (a : Fin 3) (y : E3) : ℝ := fderiv ℝ (φL x₀ L) y (LogBound.eb a)
def df (f : E3 → E3) (m a : Fin 3) (y : E3) : ℝ := fderiv ℝ (fun z => f z m) y (LogBound.eb a)

lemma D_Gs (a m : Fin 3) (y : E3) :
    (∂_{LogBound.eb a} (Gs hf x₀ hL m)) y = ((dφ x₀ L a y * f y m + φL x₀ L y * df f m a y : ℝ) : ℂ) := by
  rw [Gs.eq_def, lineDeriv_toS]
  congr 1
  rw [fderiv_fun_mul ((contDiff_φL x₀ L).differentiable (by simp) y)
    ((contDiff_comp hf m).differentiable (by simp) y)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, dφ, df]
  ring

include hL in
lemma dφ_at (a : Fin 3) : dφ x₀ L a x₀ = 0 := by
  unfold dφ
  rw [(φL_eventually_one x₀ hL).fderiv_eq]; simp

include hL in
lemma norm_dφ_le {B : ℕ → ℝ}
    (hB : ∀ i y, ‖iteratedFDeriv ℝ i (fun ξ : E3 => LogBound.ρ ξ) y‖ ≤ B i)
    (a : Fin 3) (y : E3) : |dφ x₀ L a y| ≤ B 1 * L⁻¹ := by
  have h := norm_iter_φL_le hB x₀ hL 1 y
  rw [norm_iteratedFDeriv_one, pow_one] at h
  unfold dφ
  rw [← Real.norm_eq_abs]
  refine ((fderiv ℝ (φL x₀ L) y).le_opNorm _).trans ?_
  rw [PiLp.norm_single, norm_one, mul_one]
  exact h

lemma D_Gs_at (k l : Fin 3) :
    (∂_{LogBound.eb k} (Gs hf x₀ hL l)) x₀ = ((df f l k x₀ : ℝ) : ℂ) := by
  rw [D_Gs, dφ_at x₀ hL, φL_eq_one x₀ hL (by simp; exact hL.le)]
  simp

open NavierStokes3D in
lemma curl_Gs_le {B : ℕ → ℝ}
    (hB : ∀ i y, ‖iteratedFDeriv ℝ i (fun ξ : E3 => LogBound.ρ ξ) y‖ ≤ B i)
    {F Ω : ℝ} (hF : ∀ y m, |f y m| ≤ F) (hΩ : ∀ y, ‖vorticity f y‖ ≤ Ω) (l m : Fin 3) (y : E3) :
    ‖(∂_{LogBound.eb m} (Gs hf x₀ hL l) - ∂_{LogBound.eb l} (Gs hf x₀ hL m)) y‖ ≤
      Ω + 2 * (B 1 * L⁻¹) * F := by
  rw [SchwartzMap.sub_apply, D_Gs, D_Gs, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]
  have e : dφ x₀ L m y * f y l + φL x₀ L y * df f l m y -
      (dφ x₀ L l y * f y m + φL x₀ L y * df f m l y) =
      dφ x₀ L m y * f y l - dφ x₀ L l y * f y m + φL x₀ L y * (df f l m y - df f m l y) := by
    ring
  rw [e]
  have h1 := norm_dφ_le x₀ hL hB m y
  have h2 := norm_dφ_le x₀ hL hB l y
  have h3 : |df f l m y - df f m l y| ≤ Ω := (abs_curl_pair_le f y m l).trans (hΩ y)
  have hφ0 := φL_nonneg x₀ L y; have hφ1 := φL_le_one x₀ L y
  have hF0 : 0 ≤ F := (abs_nonneg _).trans (hF y 0)
  have hb0 : 0 ≤ B 1 * L⁻¹ := (abs_nonneg _).trans h1
  calc _ ≤ |dφ x₀ L m y * f y l| + |dφ x₀ L l y * f y m| +
        |φL x₀ L y * (df f l m y - df f m l y)| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_sub _ _
    _ ≤ (B 1 * L⁻¹) * F + (B 1 * L⁻¹) * F + 1 * Ω := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hφ0]
        gcongr
        · exact hF y l
        · exact hF y m
    _ = _ := by ring

open NavierStokes3D in
lemma div_Gs_le {B : ℕ → ℝ}
    (hB : ∀ i y, ‖iteratedFDeriv ℝ i (fun ξ : E3 => LogBound.ρ ξ) y‖ ≤ B i)
    (hdiv : ∀ y, div f y = 0) {F : ℝ} (hF : ∀ y m, |f y m| ≤ F) (y : E3) :
    ‖(∑ m : Fin 3, ∂_{LogBound.eb m} (Gs hf x₀ hL m) : 𝓢(E3, ℂ)) y‖ ≤ 3 * ((B 1 * L⁻¹) * F) := by
  rw [SchwartzMap.sum_apply]
  simp only [D_Gs]
  rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
  have hd : ∑ m : Fin 3, df f m m y = 0 := by
    have := hdiv y; simpa [div, df] using this
  have e : ∑ m : Fin 3, (dφ x₀ L m y * f y m + φL x₀ L y * df f m m y) =
      ∑ m : Fin 3, dφ x₀ L m y * f y m := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hd, mul_zero, add_zero]
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ _m : Fin 3, (B 1 * L⁻¹) * F := Finset.sum_le_sum fun m _ => by
        rw [abs_mul]
        exact mul_le_mul (norm_dφ_le x₀ hL hB m y) (hF y m) (abs_nonneg _)
          ((abs_nonneg _).trans (norm_dφ_le x₀ hL hB m y))
    _ = _ := by simp

lemma l2_Gs_le (l : Fin 3) :
    ∫⁻ y, ‖Gs hf x₀ hL l y‖ₑ ^ (2 : ℝ) ≤ ∫⁻ y, ‖f y‖ₑ ^ 2 := by
  refine lintegral_mono fun y => ?_
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  gcongr
  rw [Gs.eq_def, toS_apply, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, Complex.norm_real]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (φL_nonneg x₀ L y)]
  calc _ ≤ 1 * |f y l| := mul_le_mul_of_nonneg_right (φL_le_one x₀ L y) (abs_nonneg _)
    _ = ‖f y l‖ := by rw [one_mul, Real.norm_eq_abs]
    _ ≤ ‖f y‖ := PiLp.norm_apply_le _ _

lemma contDiff_dφ (a : Fin 3) : ContDiff ℝ ∞ (dφ x₀ L a) :=
  ((contDiff_φL x₀ L).fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

include hL in
lemma hasCompactSupport_dφ (a : Fin 3) : HasCompactSupport (dφ x₀ L a) :=
  ((hasCompactSupport_φL x₀ hL).fderiv (𝕜 := ℝ)).comp_left
    (g := fun T : E3 →L[ℝ] ℝ => T (LogBound.eb a)) (by simp)

include hf in
lemma contDiff_df (m a : Fin 3) : ContDiff ℝ ∞ (df f m a) :=
  ((contDiff_comp hf m).fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

/-- The two Leibniz pieces of `∂_k G_l`. -/
def S1 (k l : Fin 3) : 𝓢(E3, ℂ) :=
  toS ((contDiff_dφ x₀ k).mul (contDiff_comp hf l)) (hasCompactSupport_dφ x₀ hL k).mul_right
def S2 (k l : Fin 3) : 𝓢(E3, ℂ) :=
  toS ((contDiff_φL x₀ L).mul (contDiff_df hf l k)) (hasCompactSupport_φL x₀ hL).mul_right

lemma D_eq_S (k l : Fin 3) :
    ∂_{LogBound.eb k} (Gs hf x₀ hL l) = S1 hf x₀ hL k l + S2 hf x₀ hL k l := by
  ext y
  rw [D_Gs, SchwartzMap.add_apply, S1, S2, toS_apply, toS_apply]
  push_cast; ring

lemma sub_lap_add (a b : 𝓢(E3, ℂ)) :
    (a + b) - Laplacian.laplacian (a + b) =
      (a - Laplacian.laplacian a) + (b - Laplacian.laplacian b) := by
  rw [← SchwartzMap.laplacianCLM_eq' (a + b), map_add, SchwartzMap.laplacianCLM_eq',
    SchwartzMap.laplacianCLM_eq']
  abel

/-- **`‖(1-Δ)∂_k G_l‖₂ ≲ ‖f‖_{H³}`, uniformly in `L ≥ 1`.** -/
lemma high_Gs_le {B : ℕ → ℝ}
    (hB : ∀ i y, ‖iteratedFDeriv ℝ i (fun ξ : E3 => LogBound.ρ ξ) y‖ ≤ B i) (hL1 : 1 ≤ L)
    (k l : Fin 3) :
    (∫⁻ y, ‖(∂_{LogBound.eb k} (Gs hf x₀ hL l) -
        Laplacian.laplacian (∂_{LogBound.eb k} (Gs hf x₀ hL l))) y‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
      (ENNReal.ofReal (27 * (4 * B 1 + 6 * B 2 + 3 * B 3) ^ 2) *
          R3BKM.sobolevEnergy 3 f) ^ (1 / 2 : ℝ) +
      (ENNReal.ofReal (27 * (4 * B 0 + 6 * B 1 + 3 * B 2) ^ 2) *
          R3BKM.sobolevEnergy 3 f) ^ (1 / 2 : ℝ) := by
  have hLi : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL1
  have hLi0 : 0 ≤ L⁻¹ := (inv_pos.2 hL).le
  have hpow : ∀ i : ℕ, (L⁻¹) ^ i ≤ 1 := fun i => pow_le_one₀ hLi0 hLi
  have hB0 : ∀ i, 0 ≤ B i := fun i => (norm_nonneg _).trans (hB i 0)
  have hφB : ∀ i y, ‖iteratedFDeriv ℝ i (φL x₀ L) y‖ ≤ B i := fun i y =>
    (norm_iter_φL_le hB x₀ hL i y).trans (mul_le_of_le_one_right (hB0 i) (hpow i))
  have hdφB : ∀ i y, ‖iteratedFDeriv ℝ i (dφ x₀ L k) y‖ ≤ B (i + 1) := fun i y => by
    have := norm_iter_dir_le (contDiff_φL x₀ L) (LogBound.eb k) i y
    rw [PiLp.norm_single, norm_one, one_mul] at this
    exact this.trans (hφB (i + 1) y)
  have h1 := leibniz_L2 (contDiff_dφ x₀ k) (contDiff_comp hf l) (fun i => B (i + 1)) hdφB
    (S1 hf x₀ hL k l) rfl
  have h2 := leibniz_L2 (contDiff_φL x₀ L) (contDiff_df hf l k) B hφB (S2 hf x₀ hL k l) rfl
  have e1 : energyR 2 (fun y => f y l) ≤ R3BKM.sobolevEnergy 3 f := energyR_comp_le hf l
  have hdkj : df f l k = GradBound.dkj f k l := by
    funext y
    exact comp_fderiv ((hf.differentiable (by simp)) y) l _
  have e2 : energyR 2 (df f l k) ≤ R3BKM.sobolevEnergy 3 f := by
    rw [hdkj]; exact GradBound.energyR_dkj_le hf k l
  rw [D_eq_S, sub_lap_add]
  set A := S1 hf x₀ hL k l - Laplacian.laplacian (S1 hf x₀ hL k l)
  set C := S2 hf x₀ hL k l - Laplacian.laplacian (S2 hf x₀ hL k l)
  have hmA : AEMeasurable (fun y => ‖A y‖ₑ) := A.continuous.enorm.measurable.aemeasurable
  have hmC : AEMeasurable (fun y => ‖C y‖ₑ) := C.continuous.enorm.measurable.aemeasurable
  calc _ ≤ (∫⁻ y, ((fun y => ‖A y‖ₑ) + fun y => ‖C y‖ₑ) y ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        gcongr with y
        rw [SchwartzMap.add_apply]
        exact enorm_add_le _ _
    _ ≤ _ := ENNReal.lintegral_Lp_add_le hmA hmC (by norm_num)
    _ ≤ _ := by
        gcongr
        · exact h1.trans (by gcongr)
        · exact h2.trans (by gcongr)

include hf hL in
open NavierStokes3D in
/-- **Pointwise frequency-truncated bound for smooth divergence-free fields** (all `N`, `L ≥ 1`). -/
lemma pt_bound {B : ℕ → ℝ}
    (hB : ∀ i y, ‖iteratedFDeriv ℝ i (fun ξ : E3 => LogBound.ρ ξ) y‖ ≤ B i) (hL1 : 1 ≤ L)
    (hdiv : ∀ y, div f y = 0) {F Ω : ℝ} (hF : ∀ y m, |f y m| ≤ F)
    (hΩ : ∀ y, ‖vorticity f y‖ ≤ Ω) (k l : Fin 3) (N : ℕ) :
    ENNReal.ofReal |df f l k x₀| ≤
      LogBound.Clow * (∫⁻ y, ‖f y‖ₑ ^ 2) ^ (1 / 2 : ℝ) +
      ENNReal.ofReal (N * (LogBound.Akern * (3 * (Ω + 2 * (B 1 * L⁻¹) * F) +
        3 * ((B 1 * L⁻¹) * F)))) +
      (ENNReal.ofReal (Real.sqrt ((2 : ℝ) ^ N))⁻¹ * LogBound.Kh) ^ (1 / 2 : ℝ) *
      ((ENNReal.ofReal (27 * (4 * B 1 + 6 * B 2 + 3 * B 3) ^ 2) *
          R3BKM.sobolevEnergy 3 f) ^ (1 / 2 : ℝ) +
      (ENNReal.ofReal (27 * (4 * B 0 + 6 * B 1 + 3 * B 2) ^ 2) *
          R3BKM.sobolevEnergy 3 f) ^ (1 / 2 : ℝ)) := by
  have hmain := LogBound.schwartz_log_bound (fun m => Gs hf x₀ hL m) k l N
    (Bω := Ω + 2 * (B 1 * L⁻¹) * F) (Bd := 3 * ((B 1 * L⁻¹) * F))
    (fun m y => curl_Gs_le hf x₀ hL hB hF hΩ l m y) (fun y => div_Gs_le hf x₀ hL hB hdiv hF y) x₀
  rw [D_Gs_at hf x₀ hL k l, ← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs] at hmain
  refine hmain.trans ?_
  have h1 := ENNReal.rpow_le_rpow (l2_Gs_le hf x₀ hL l) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  refine add_le_add (add_le_add (mul_le_mul_right ?_ _) le_rfl)
    (mul_le_mul_right (high_Gs_le hf x₀ hL hB hL1 k l) _)
  exact h1

end Localize


/-! ## Arithmetic of the truncation parameters -/

lemma two_pow_ceil_ge (E : ℝ) (hE : 0 ≤ E) :
    (1 + E) ^ 2 ≤ (2 : ℝ) ^ (⌈3 * Real.log (1 + E)⌉₊) := by
  set N := ⌈3 * Real.log (1 + E)⌉₊
  have hlog : 0 ≤ Real.log (1 + E) := Real.log_nonneg (by linarith)
  have hN : 3 * Real.log (1 + E) ≤ N := Nat.le_ceil _
  have hl2 := Real.log_two_gt_d9
  have h1 : (1 + E) ^ 2 = Real.exp (2 * Real.log (1 + E)) := by
    rw [show (2 : ℝ) * Real.log (1 + E) = Real.log ((1 + E) ^ 2) by
      rw [Real.log_pow]; norm_num, Real.exp_log (by positivity)]
  have h2 : (2 : ℝ) ^ N = Real.exp (N * Real.log 2) := by
    rw [← Real.log_rpow (by norm_num), Real.exp_log (by positivity), Real.rpow_natCast]
  rw [h1, h2, Real.exp_le_exp]
  nlinarith

lemma sqrt_le_one_add {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ 1 + x := by
  rcases le_total x 1 with h | h
  · have := Real.sqrt_le_one.mpr h; linarith
  · have : Real.sqrt x ≤ x := (Real.sqrt_le_left (by linarith)).2 (by nlinarith)
    linarith


open NavierStokes3D in
lemma norm_vort_le {f : E3 → E3} (hf : Differentiable ℝ f) (y : E3) :
    ‖vorticity f y‖ ≤ 6 * ‖fderiv ℝ f y‖ := by
  have hd : ∀ a b : Fin 3, |fderiv ℝ (fun z => f z a) y (EuclideanSpace.single b 1)| ≤
      ‖fderiv ℝ f y‖ := fun a b => abs_dc_le (hf y) a b
  have hs : ∀ a b c d : Fin 3, |fderiv ℝ (fun z => f z a) y (EuclideanSpace.single b 1) -
      fderiv ℝ (fun z => f z c) y (EuclideanSpace.single d 1)| ≤ 2 * ‖fderiv ℝ f y‖ :=
    fun a b c d => (abs_sub _ _).trans (by linarith [hd a b, hd c d])
  refine (GradBound.norm_le_sum_coord _).trans ?_
  rw [Fin.sum_univ_three]
  simp only [vorticity, curl, directionalCoord, PiLp.add_apply, PiLp.single_apply]
  simp
  linarith [hs 2 1 1 2, hs 0 2 2 0, hs 1 0 0 1]


/-! ## The BKM logarithmic inequality, as stated at `R3BKMContinuation.lean:58` -/

lemma rpow_half_le_one_add (x : ℝ) (hx : 0 ≤ x) :
    (ENNReal.ofReal x) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (1 + x) := by
  rw [ENNReal.ofReal_rpow_of_nonneg hx (by norm_num), ← Real.sqrt_eq_rpow]
  exact ENNReal.ofReal_le_ofReal (sqrt_le_one_add hx)

open NavierStokes3D in
/-- Core pointwise estimate with explicit absolute constants. -/
lemma pt_final {B : ℕ → ℝ}
    (hB : ∀ i y, ‖iteratedFDeriv ℝ i (fun ξ : E3 => LogBound.ρ ξ) y‖ ≤ B i)
    {f : E3 → E3} (hf : ContDiff ℝ ∞ f) (hdiv : ∀ y, div f y = 0)
    (hE : R3BKM.sobolevEnergy 3 f < ⊤) {Ω : ℝ} (hΩ0 : 0 ≤ Ω) (hΩ : ∀ y, ‖vorticity f y‖ ≤ Ω)
    (k l : Fin 3) (x₀ : E3) :
    |df f l k x₀| ≤ LogBound.Clow.toReal * (1 + R3BKM.l2Sq f) +
      9 * LogBound.Akern * (Ω * (1 + Real.log (1 + R3BKM.hsSq 3 f))) +
      9 * LogBound.Akern * B 1 +
      (LogBound.Kh ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal (27 * (4 * B 1 + 6 * B 2 + 3 * B 3) ^ 2) ^ (1 / 2 : ℝ) +
         ENNReal.ofReal (27 * (4 * B 0 + 6 * B 1 + 3 * B 2) ^ 2) ^ (1 / 2 : ℝ))).toReal := by
  set E := R3BKM.hsSq 3 f
  have hE0 : 0 ≤ E := ENNReal.toReal_nonneg
  have hEe : R3BKM.sobolevEnergy 3 f = ENNReal.ofReal E := (ENNReal.ofReal_toReal hE.ne).symm
  set l2 := R3BKM.l2Sq f
  have hl20 : 0 ≤ l2 := ENNReal.toReal_nonneg
  have hl2e : (∫⁻ y, ‖f y‖ₑ ^ 2) = ENNReal.ofReal l2 :=
    (ENNReal.ofReal_toReal ((l2_le_energy f).trans_lt hE).ne).symm
  have hB0 : ∀ i, 0 ≤ B i := fun i => (norm_nonneg _).trans (hB i 0)
  set F := 8 * Real.sqrt E
  have hF0 : 0 ≤ F := by positivity
  have hF : ∀ y m, |f y m| ≤ F := fun y m => by
    have := SobolevBridge.abs_component_le_sobolevEnergy hf m y
    rw [hEe, ENNReal.ofReal_rpow_of_nonneg hE0 (by norm_num), ← Real.sqrt_eq_rpow,
      show (8 : ℝ≥0∞) = ENNReal.ofReal 8 by simp, ← ENNReal.ofReal_mul (by norm_num)] at this
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 this
  set N := ⌈3 * Real.log (1 + E)⌉₊
  set L : ℝ := 1 + N * F
  have hL1 : 1 ≤ L := by have : (0 : ℝ) ≤ N * F := by positivity
                         linarith
  have hL : 0 < L := by linarith
  have hpt := pt_bound hf x₀ hL hB hL1 hdiv hF hΩ k l N
  set A := LogBound.Akern
  have hA : 0 ≤ A := by
    unfold A LogBound.Akern
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      integral_nonneg fun _ => norm_nonneg _
  -- low term
  have hT1 : LogBound.Clow * (∫⁻ y, ‖f y‖ₑ ^ 2) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (LogBound.Clow.toReal * (1 + l2)) := by
    rw [hl2e, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal LogBound.Clow_ne_top]
    exact mul_le_mul_right (rpow_half_le_one_add l2 hl20) _
  -- middle term
  have hlog : 0 ≤ Real.log (1 + E) := Real.log_nonneg (by linarith)
  have hN : (N : ℝ) ≤ 3 * (1 + Real.log (1 + E)) := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 3 * Real.log (1 + E) by positivity)
    linarith
  have hNF : (N : ℝ) * F * L⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ hL, one_mul]; linarith
  have hT2 : (N : ℝ) * (A * (3 * (Ω + 2 * (B 1 * L⁻¹) * F) + 3 * ((B 1 * L⁻¹) * F))) ≤
      9 * A * (Ω * (1 + Real.log (1 + E))) + 9 * A * B 1 := by
    have e : (N : ℝ) * (A * (3 * (Ω + 2 * (B 1 * L⁻¹) * F) + 3 * ((B 1 * L⁻¹) * F))) =
        3 * A * Ω * N + 9 * A * B 1 * (N * F * L⁻¹) := by ring
    rw [e]
    have h1 : 3 * A * Ω * N ≤ 3 * A * Ω * (3 * (1 + Real.log (1 + E))) :=
      mul_le_mul_of_nonneg_left hN (by positivity)
    have h2 : 9 * A * B 1 * (N * F * L⁻¹) ≤ 9 * A * B 1 * 1 :=
      mul_le_mul_of_nonneg_left hNF (by have := hB0 1; positivity)
    nlinarith
  -- high term
  set c1 := ENNReal.ofReal (27 * (4 * B 1 + 6 * B 2 + 3 * B 3) ^ 2)
  set c2 := ENNReal.ofReal (27 * (4 * B 0 + 6 * B 1 + 3 * B 2) ^ 2)
  set Ch := LogBound.Kh ^ (1 / 2 : ℝ) * (c1 ^ (1 / 2 : ℝ) + c2 ^ (1 / 2 : ℝ))
  have hCh : Ch ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) LogBound.Kh_ne_top)
      (ENNReal.add_ne_top.2 ⟨ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top,
        ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top⟩)
  have hsmall : (Real.sqrt ((2 : ℝ) ^ N))⁻¹ * E ≤ 1 := by
    have h2N := two_pow_ceil_ge E hE0
    have hs : E ≤ Real.sqrt ((2 : ℝ) ^ N) := by
      rw [Real.le_sqrt hE0 (by positivity)]
      nlinarith
    have hpos : 0 < Real.sqrt ((2 : ℝ) ^ N) := Real.sqrt_pos.2 (by positivity)
    rw [inv_mul_le_iff₀ hpos, mul_one]; exact hs
  have hT3 : (ENNReal.ofReal (Real.sqrt ((2 : ℝ) ^ N))⁻¹ * LogBound.Kh) ^ (1 / 2 : ℝ) *
      ((c1 * R3BKM.sobolevEnergy 3 f) ^ (1 / 2 : ℝ) +
        (c2 * R3BKM.sobolevEnergy 3 f) ^ (1 / 2 : ℝ)) ≤ Ch := by
    set a := ENNReal.ofReal (Real.sqrt ((2 : ℝ) ^ N))⁻¹
    have hh : (0 : ℝ) ≤ 1 / 2 := by norm_num
    rw [ENNReal.mul_rpow_of_nonneg _ _ hh, ENNReal.mul_rpow_of_nonneg _ _ hh,
      ENNReal.mul_rpow_of_nonneg _ _ hh]
    have hae : a ^ (1 / 2 : ℝ) * R3BKM.sobolevEnergy 3 f ^ (1 / 2 : ℝ) ≤ 1 := by
      rw [← ENNReal.mul_rpow_of_nonneg _ _ hh, hEe, ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.rpow_le_one ?_ hh
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hsmall
    calc a ^ (1 / 2 : ℝ) * LogBound.Kh ^ (1 / 2 : ℝ) *
          (c1 ^ (1 / 2 : ℝ) * R3BKM.sobolevEnergy 3 f ^ (1 / 2 : ℝ) +
            c2 ^ (1 / 2 : ℝ) * R3BKM.sobolevEnergy 3 f ^ (1 / 2 : ℝ))
        = Ch * (a ^ (1 / 2 : ℝ) * R3BKM.sobolevEnergy 3 f ^ (1 / 2 : ℝ)) := by
          simp only [Ch]; ring
      _ ≤ Ch * 1 := mul_le_mul_right hae _
      _ = Ch := mul_one _
  have htot := hpt.trans (add_le_add (add_le_add hT1 (ENNReal.ofReal_le_ofReal hT2)) hT3)
  rw [← ENNReal.ofReal_toReal hCh, ← ENNReal.ofReal_add (by positivity) (by
      have := hB0 1; positivity), ← ENNReal.ofReal_add (by
      have := hB0 1; have := LogBound.Clow.toReal; positivity) ENNReal.toReal_nonneg] at htot
  have := (ENNReal.ofReal_le_ofReal_iff (by
    have := hB0 1; positivity)).1 htot
  linarith


open NavierStokes3D in
/-- **The BKM logarithmic inequality** (`R3BKM.BKMLogInequality`, `R3BKMContinuation.lean:58`),
proved as stated: for smooth divergence-free `f` with finite `H³` energy, `∇f` is bounded and
`‖∇f‖_∞ ≤ C (1 + ‖f‖₂² + ‖curl f‖_∞ (1 + log (1 + ‖f‖²_{H³})))`. -/
theorem bkmLogInequality : R3BKM.BKMLogInequality := by
  obtain ⟨B, hB⟩ := exists_bump_bounds
  have hB0 : ∀ i, 0 ≤ B i := fun i => (norm_nonneg _).trans (hB i 0)
  have hA : 0 ≤ LogBound.Akern := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      integral_nonneg fun _ => norm_nonneg _
  set Chr := (LogBound.Kh ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal (27 * (4 * B 1 + 6 * B 2 + 3 * B 3) ^ 2) ^ (1 / 2 : ℝ) +
         ENNReal.ofReal (27 * (4 * B 0 + 6 * B 1 + 3 * B 2) ^ 2) ^ (1 / 2 : ℝ))).toReal
  set C0 : ℝ := LogBound.Clow.toReal + 9 * LogBound.Akern + 9 * LogBound.Akern * B 1 + Chr + 1
  have hC0 : 0 < C0 := by
    have := hB0 1
    have : 0 ≤ Chr := ENNReal.toReal_nonneg
    have : 0 ≤ LogBound.Clow.toReal := ENNReal.toReal_nonneg
    positivity
  refine ⟨9 * C0, by positivity, fun f hf hdiv hE => ⟨GradBound.bddAbove_norm_fderiv hf hE, ?_⟩⟩
  obtain ⟨M, hM⟩ := GradBound.bddAbove_norm_fderiv hf hE
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hωb : BddAbove (Set.range fun y => ‖vorticity f y‖) :=
    ⟨6 * M, by
      rintro _ ⟨y, rfl⟩
      exact (norm_vort_le hfd y).trans (by linarith [hM ⟨y, rfl⟩])⟩
  set Ω := vorticity_sup_norm (vorticity f)
  have hΩ : ∀ y, ‖vorticity f y‖ ≤ Ω := fun y => le_ciSup hωb y
  have hΩ0 : 0 ≤ Ω := vorticity_sup_norm_nonneg _
  set X := 1 + R3BKM.l2Sq f + Ω * (1 + Real.log (1 + R3BKM.hsSq 3 f))
  have hl2 : 0 ≤ R3BKM.l2Sq f := ENNReal.toReal_nonneg
  have hlog : 0 ≤ Real.log (1 + R3BKM.hsSq 3 f) :=
    Real.log_nonneg (by have := R3BKM.hsSq_nonneg 3 f; linarith)
  have hX : 1 ≤ X := by have : 0 ≤ Ω * (1 + Real.log (1 + R3BKM.hsSq 3 f)) := by positivity
                        linarith
  have hpt : ∀ k l x₀, |df f l k x₀| ≤ C0 * X := fun k l x₀ => by
    have h := pt_final hB hf hdiv hE hΩ0 hΩ k l x₀
    have h1 : LogBound.Clow.toReal * (1 + R3BKM.l2Sq f) ≤ LogBound.Clow.toReal * X :=
      mul_le_mul_of_nonneg_left (by
        have : 0 ≤ Ω * (1 + Real.log (1 + R3BKM.hsSq 3 f)) := by positivity
        linarith) ENNReal.toReal_nonneg
    have h2 : 9 * LogBound.Akern * (Ω * (1 + Real.log (1 + R3BKM.hsSq 3 f))) ≤
        9 * LogBound.Akern * X := mul_le_mul_of_nonneg_left (by
          have : 0 ≤ Ω * (1 + Real.log (1 + R3BKM.hsSq 3 f)) := by positivity
          linarith) (by positivity)
    have h3 : 9 * LogBound.Akern * B 1 ≤ 9 * LogBound.Akern * B 1 * X :=
      le_mul_of_one_le_right (by have := hB0 1; positivity) hX
    have h4 : Chr ≤ Chr * X := le_mul_of_one_le_right ENNReal.toReal_nonneg hX
    have h5 : 0 ≤ X := by linarith
    calc _ ≤ _ := h
      _ ≤ LogBound.Clow.toReal * X + 9 * LogBound.Akern * X + 9 * LogBound.Akern * B 1 * X +
          Chr * X := by linarith
      _ ≤ C0 * X := by simp only [C0]; nlinarith
  refine ciSup_le fun x₀ => ?_
  refine (GradBound.norm_clm_le _).trans ?_
  calc _ ≤ ∑ k : Fin 3, ∑ l : Fin 3, |df f l k x₀| := Finset.sum_le_sum fun k _ => by
        refine (GradBound.norm_le_sum_coord _).trans (le_of_eq (Finset.sum_congr rfl fun l _ => ?_))
        rw [df, comp_fderiv (hfd x₀)]
    _ ≤ ∑ _k : Fin 3, ∑ _l : Fin 3, C0 * X :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hpt k l x₀
    _ = 9 * C0 * X := by simp; ring
    _ = _ := by ring

open NavierStokes3D FrohmanianTether RepairedTether R3BKM in
/-- `Clay_A_Fefferman` now needs only the tether rate and the Kato maximal solution. -/
theorem clay_A_fefferman_of_rate_of_kato
    (hrate : ∀ ν > (0 : ℝ), ∀ u₀ : VelocityField, ContDiff ℝ ∞ u₀ → (∀ x, div u₀ x = 0) →
      FeffermanDecay u₀ → FrohmanianTetherRateSmooth u₀ ν)
    (hK : ∀ ν > (0 : ℝ), ∀ u₀ : VelocityField, ContDiff ℝ ∞ u₀ → (∀ x, div u₀ x = 0) →
      FeffermanDecay u₀ → KatoMaximalSolution ν u₀) :
    Clay_A_Fefferman :=
  clay_A_fefferman_of_rate_of_kato_of_log hrate bkmLogInequality hK

end LogBoundLocal

#print axioms LogBoundLocal.clay_A_fefferman_of_rate_of_kato
#print axioms LogBoundLocal.leibniz_L2
#print axioms LogBoundLocal.high_Gs_le
#print axioms LogBoundLocal.pt_bound
#print axioms LogBoundLocal.pt_final
#print axioms LogBoundLocal.bkmLogInequality
