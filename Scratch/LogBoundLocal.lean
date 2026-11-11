import Scratch.LogBound
import Scratch.GradBound
import Scratch.SobolevBridge

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

end LogBoundLocal

#print axioms LogBoundLocal.leibniz_L2
