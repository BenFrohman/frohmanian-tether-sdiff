import Scratch.FourierEmbedding
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Algebra.Order.Chebyshev

/-! # `H² ↪ L^∞` on ℝ³ for every smooth function (no decay assumed)

Localize with a translated bump, apply the Schwartz-class Fourier bound
`FourierEmb.enorm_le_weight_L2`, and bound `φ f - Δ(φ f)` by the multi-index `H²` energy. -/

open MeasureTheory SchwartzMap FourierTransform Real
open scoped ENNReal Laplacian ContDiff

noncomputable section
namespace FourierCutoff

open FourierEmb

/-- Unit-vector tuple of a word `α`. -/
abbrev U {k : ℕ} (α : Fin k → Fin 3) : Fin k → E3 := fun j => EuclideanSpace.single (α j) (1 : ℝ)

/-- Scalar multi-index `H^m` energy (same convention as `R3BKM.sobolevEnergy`). -/
def energyR (m : ℕ) (f : E3 → ℝ) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range (m + 1), ∑ α : Fin k → Fin 3,
    ∫⁻ x, ‖iteratedFDeriv ℝ k f x (U α)‖ₑ ^ 2

lemma eq_sum_basis (y : E3) : y = ∑ i : Fin 3, y i • EuclideanSpace.single i (1 : ℝ) := by
  ext l; simp [Finset.sum_apply, Pi.single_apply]

/-- Operator norm of a multilinear form on ℝ³ is at most the sum of its values on basis tuples. -/
lemma norm_le_sum_basis {k : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin k => E3) ℝ) :
    ‖M‖ ≤ ∑ α : Fin k → Fin 3, ‖M (U α)‖ := by
  refine M.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun v => ?_
  have hv : M v = M (fun j => ∑ i : Fin 3, v j i • EuclideanSpace.single i (1 : ℝ)) :=
    congrArg M (funext fun j => eq_sum_basis (v j))
  have hs : M (fun j => ∑ i : Fin 3, v j i • EuclideanSpace.single i (1 : ℝ)) =
      ∑ r : Fin k → Fin 3, (∏ j, v j (r j)) • M (U r) := by
    rw [M.map_sum]
    exact Finset.sum_congr rfl fun r _ => M.map_smul_univ (fun j => v j (r j)) (U r)
  rw [hv, hs]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun r _ => ?_
  rw [norm_smul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun j _ => PiLp.norm_apply_le _ _

set_option backward.isDefEq.respectTransparency false in
/-- `|Δ g| ≤ 3 ‖D² g‖` on ℝ³. -/
lemma norm_laplacian_le (g : E3 → ℂ) (y : E3) : ‖Δ g y‖ ≤ 3 * ‖iteratedFDeriv ℝ 2 g y‖ := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis g
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  refine (norm_sum_le _ _).trans ?_
  have : ∀ i : Fin 3, ‖iteratedFDeriv ℝ 2 g y ![EuclideanSpace.basisFun (Fin 3) ℝ i,
      EuclideanSpace.basisFun (Fin 3) ℝ i]‖ ≤ ‖iteratedFDeriv ℝ 2 g y‖ := fun i => by
    refine ((iteratedFDeriv ℝ 2 g y).le_opNorm _).trans (le_of_eq ?_)
    simp [Fin.prod_univ_two]
  refine (Finset.sum_le_sum fun i _ => this i).trans (le_of_eq ?_)
  simp

/-- Pointwise: `‖D^k f y‖ ≤ ∑_α |D^k f y (U α)|`. -/
lemma norm_iter_le (f : E3 → ℝ) (k : ℕ) (y : E3) :
    ‖iteratedFDeriv ℝ k f y‖ ≤ ∑ α : Fin k → Fin 3, ‖iteratedFDeriv ℝ k f y (U α)‖ :=
  norm_le_sum_basis _

/-- `(∑_{k≤2} S_k)² ≤ 27 ∑_{k≤2} ∑_α a_{k,α}²` where `S_k = ∑_α a_{k,α}`. -/
lemma sq_le_energy_pt (f : E3 → ℝ) (y : E3) :
    (∑ k ∈ Finset.range 3, ∑ α : Fin k → Fin 3, ‖iteratedFDeriv ℝ k f y (U α)‖) ^ 2 ≤
      27 * ∑ k ∈ Finset.range 3, ∑ α : Fin k → Fin 3, ‖iteratedFDeriv ℝ k f y (U α)‖ ^ 2 := by
  have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.range 3)
    (f := fun k => ∑ α : Fin k → Fin 3, ‖iteratedFDeriv ℝ k f y (U α)‖)
  have h2 : ∀ k ∈ Finset.range 3, (∑ α : Fin k → Fin 3, ‖iteratedFDeriv ℝ k f y (U α)‖) ^ 2 ≤
      9 * ∑ α : Fin k → Fin 3, ‖iteratedFDeriv ℝ k f y (U α)‖ ^ 2 := by
    intro k hk
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin k → Fin 3)))
      (f := fun α => ‖iteratedFDeriv ℝ k f y (U α)‖)
    refine this.trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => by positivity))
    have hk3 : k ≤ 2 := by simp at hk; omega
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    have : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk3
    exact_mod_cast this.trans (by norm_num)
  simp only [Finset.card_range] at h1
  calc _ ≤ (3 : ℝ) * ∑ k ∈ Finset.range 3,
        (∑ α : Fin k → Fin 3, ‖iteratedFDeriv ℝ k f y (U α)‖) ^ 2 := by exact_mod_cast h1
    _ ≤ 3 * ∑ k ∈ Finset.range 3, 9 * ∑ α : Fin k → Fin 3, ‖iteratedFDeriv ℝ k f y (U α)‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum h2) (by norm_num)
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- **`H² ↪ L^∞` on ℝ³ for smooth functions.** One absolute constant `C < ∞` with
`|f x| ≤ C ‖f‖_{H²}` for every smooth `f : ℝ³ → ℝ` and every `x` (no decay assumed). -/
theorem abs_le_energyR :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f : E3 → ℝ, ContDiff ℝ ∞ f → ∀ x : E3,
      ENNReal.ofReal |f x| ≤ C * energyR 2 f ^ (1 / 2 : ℝ) := by
  let ρ : ContDiffBump (0 : E3) := ⟨1, 2, one_pos, one_lt_two⟩
  have hb : ∀ i : ℕ, ∃ B : ℝ, ∀ y, ‖iteratedFDeriv ℝ i ρ y‖ ≤ B := fun i => by
    obtain ⟨B, hB⟩ := ((ρ.contDiff (n := ⊤)).continuous_iteratedFDeriv
      (by exact_mod_cast le_top)).norm.bddAbove_range_of_hasCompactSupport
      (ρ.hasCompactSupport.iteratedFDeriv i).norm
    exact ⟨B, fun y => hB ⟨y, rfl⟩⟩
  choose B hB using hb
  have hB0 : ∀ i, 0 ≤ B i := fun i => (norm_nonneg _).trans (hB i 0)
  set K : ℝ := 4 * B 0 + 6 * B 1 + 3 * B 2
  have hK : 0 ≤ K := by have := hB0 0; have := hB0 1; have := hB0 2; positivity
  set Cw := (∫⁻ ξ : E3, ENNReal.ofReal (w ξ)⁻¹ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
  refine ⟨Cw * ENNReal.ofReal (27 * K ^ 2) ^ (1 / 2 : ℝ), ?_, fun f hf x => ?_⟩
  · refine ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      lintegral_w_inv_sq_lt_top.ne) (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      ENNReal.ofReal_ne_top)
  set φ : E3 → ℝ := fun y => ρ (y - x)
  have hφ : ContDiff ℝ ∞ φ := (ρ.contDiff (n := ⊤)).comp (contDiff_id.sub contDiff_const)
  have hφB : ∀ i y, ‖iteratedFDeriv ℝ i φ y‖ ≤ B i := fun i y => by
    simp only [φ]; rw [iteratedFDeriv_comp_sub]; exact hB i _
  set q : E3 → ℝ := fun y => φ y * f y
  have hq : ContDiff ℝ ∞ q := hφ.mul hf
  set g : E3 → ℂ := fun y => (q y : ℂ)
  have hg : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp hq
  have hgc : HasCompactSupport g := by
    have hφc : HasCompactSupport φ := by
      simpa [φ] using ρ.hasCompactSupport.comp_homeomorph (Homeomorph.subRight x)
    exact (hφc.mul_right (f' := f)).comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  set G : 𝓢(E3, ℂ) := hgc.toSchwartzMap hg
  have hGx : G x = (f x : ℂ) := by
    have : ρ 0 = 1 := ρ.one_of_mem_closedBall (by simp [ρ])
    simp [G, g, q, φ, this]
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
  have hpt : ∀ y, ‖(G - Δ G) y‖ ≤ K * S y := by
    intro y
    have hS0 := norm_iter_le f 0 y
    have hS1 := norm_iter_le f 1 y
    have hS2 := norm_iter_le f 2 y
    have hSdef : S y = (∑ α : Fin 0 → Fin 3, ‖iteratedFDeriv ℝ 0 f y (U α)‖) +
        (∑ α : Fin 1 → Fin 3, ‖iteratedFDeriv ℝ 1 f y (U α)‖) +
        (∑ α : Fin 2 → Fin 3, ‖iteratedFDeriv ℝ 2 f y (U α)‖) := by
      simp [S, Finset.sum_range_succ]
    have hG : (G - Δ G) y = g y - Δ g y := by
      rw [SchwartzMap.sub_apply, laplacian_apply]; rfl
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
  have hL2 : ∫⁻ y, ‖(G - Δ G) y‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (27 * K ^ 2) * energyR 2 f := by
    have hcont : ∀ (k : ℕ) (α : Fin k → Fin 3),
        Continuous fun y => iteratedFDeriv ℝ k f y (U α) := fun k α =>
      (continuous_eval_const (U α)).comp
        (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top))
    have hmeas : ∀ (k : ℕ) (α : Fin k → Fin 3),
        Measurable fun y => ‖iteratedFDeriv ℝ k f y (U α)‖ₑ ^ 2 := fun k α =>
      ((hcont k α).measurable.enorm).pow_const 2
    have hpt2 : ∀ y, ‖(G - Δ G) y‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (27 * K ^ 2) *
        ∑ k ∈ Finset.range 3, ∑ α : Fin k → Fin 3, ‖iteratedFDeriv ℝ k f y (U α)‖ₑ ^ 2 := by
      intro y
      rw [enorm_rpow_two]
      have hsq : ‖(G - Δ G) y‖ ^ 2 ≤ 27 * K ^ 2 *
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
    calc ∫⁻ y, ‖(G - Δ G) y‖ₑ ^ (2 : ℝ)
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
  have hmain := enorm_le_weight_L2 G x
  rw [hGx] at hmain
  have he : ‖(f x : ℂ)‖ₑ = ENNReal.ofReal |f x| := by
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs]
  rw [he] at hmain
  refine hmain.trans ?_
  rw [mul_assoc]
  gcongr
  calc (∫⁻ y, ‖(G - Δ G) y‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (27 * K ^ 2) * energyR 2 f) ^ (1 / 2 : ℝ) := by gcongr
    _ = _ := ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)

end FourierCutoff

#print axioms FourierCutoff.abs_le_energyR
