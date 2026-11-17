/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import Scratch.MildPressureSmooth
import Scratch.KatoPonceCommutator
import Scratch.KatoPonceHypotheses
import Scratch.DivergenceWholeSpace

/-!
 # Vanishing flux along the realized mild solution

Word derivatives of the physical fields of `Ĥ^m` slices are bounded and in
`L²`; every integrand of `WordIBP` is then dominated by a bounded multiple of
a product of two `L²` functions, and every flux is the integral of the
divergence of an integrable `C¹` field with integrable divergence, which
vanishes by `integral_div_eq_zero`.
-/

open MeasureTheory Real Filter Topology Set
open scoped ENNReal ContDiff

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
namespace MildFlux

open NavierStokes3D

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `e i`. -/
abbrev e (i : Fin 3) : E3 := EuclideanSpace.single i (1 : ℝ)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Word derivative of a general field. -/
def WD (k : ℕ) (α : Fin k → Fin 3) (f : E3 → F) : E3 → F :=
  fun x => iteratedFDeriv ℝ k f x (fun j => e (α j))

lemma continuous_WD {N k : ℕ} {f : E3 → F} (hf : ContDiff ℝ N f) (hk : k ≤ N)
    (α : Fin k → Fin 3) : Continuous (WD k α f) :=
  (continuous_eval_const (fun j => e (α j))).comp
    (hf.continuous_iteratedFDeriv (by exact_mod_cast hk))

lemma contDiff_WD {N k m : ℕ} {f : E3 → F} (hf : ContDiff ℝ N f) (hm : m + k ≤ N)
    (α : Fin k → Fin 3) : ContDiff ℝ m (WD k α f) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E3) F
      (fun j => e (α j))).contDiff.comp
    (hf.iteratedFDeriv_right (i := k) (by exact_mod_cast hm))

lemma differentiable_iter {N k : ℕ} {f : E3 → F} (hf : ContDiff ℝ N f) (hk : k + 1 ≤ N) :
    Differentiable ℝ (iteratedFDeriv ℝ k f) :=
  hf.differentiable_iteratedFDeriv (by exact_mod_cast (Nat.lt_of_succ_le hk))

lemma differentiable_WD {N k : ℕ} {f : E3 → F} (hf : ContDiff ℝ N f) (hk : k + 1 ≤ N)
    (α : Fin k → Fin 3) : Differentiable ℝ (WD k α f) := fun x =>
  ((differentiable_iter hf hk) x).continuousMultilinear_apply_const _

lemma fderiv_WD {N k : ℕ} {f : E3 → F} (hf : ContDiff ℝ N f) (hk : k + 1 ≤ N)
    (α : Fin k → Fin 3) (i : Fin 3) (x : E3) :
    fderiv ℝ (WD k α f) x (e i) = WD (k + 1) (Fin.cons i α) f x := by
  unfold WD
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) x := (differentiable_iter hf hk) x
  rw [fderiv_continuousMultilinear_apply_const_apply hd, iteratedFDeriv_succ_apply_left, Fin.cons_zero]
  congr 1

lemma norm_clm_le_sum (L : E3 →L[ℝ] F) : ‖L‖ ≤ ∑ i : Fin 3, ‖L (e i)‖ := by
  refine L.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun v => ?_
  have hv : v = ∑ i : Fin 3, v i • e i := by
    ext j; simp [e, Pi.single_apply]
  calc ‖L v‖ = ‖∑ i : Fin 3, v i • L (e i)‖ := by
        conv_lhs => rw [hv]
        simp only [map_sum, map_smul]
    _ ≤ ∑ i : Fin 3, ‖v i • L (e i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖v‖ * ‖L (e i)‖ := Finset.sum_le_sum fun i _ => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (by simpa using PiLp.norm_apply_le v i) (norm_nonneg _)
    _ = (∑ i : Fin 3, ‖L (e i)‖) * ‖v‖ := by rw [← Finset.mul_sum, mul_comm]

/-- A field all of whose word derivatives of order `≤ N` are bounded and in `L²`. -/
structure Tame (N : ℕ) (f : E3 → F) : Prop where
  smooth : ContDiff ℝ N f
  memLp : ∀ k ≤ N, ∀ α : Fin k → Fin 3, MemLp (WD k α f) 2
  bdd : ∀ k ≤ N, ∀ α : Fin k → Fin 3, ∃ C, ∀ x, ‖WD k α f x‖ ≤ C

/-- Sum of the norms of the first partials of `∂^α f`. -/
def GD (k : ℕ) (α : Fin k → Fin 3) (f : E3 → F) : E3 → ℝ :=
  fun x => ∑ i : Fin 3, ‖WD (k + 1) (Fin.cons i α) f x‖

lemma norm_fderiv_WD_le {N k : ℕ} {f : E3 → F} (hf : ContDiff ℝ N f) (hk : k + 1 ≤ N)
    (α : Fin k → Fin 3) (x : E3) : ‖fderiv ℝ (WD k α f) x‖ ≤ GD k α f x := by
  refine (norm_clm_le_sum _).trans_eq ?_
  simp only [GD, fderiv_WD hf hk]

lemma Tame.memLp_GD {N k : ℕ} {f : E3 → F} (h : Tame N f) (hk : k + 1 ≤ N)
    (α : Fin k → Fin 3) : MemLp (GD k α f) 2 := by
  unfold GD
  exact memLp_finset_sum _ fun i _ => (h.memLp (k + 1) hk (Fin.cons i α)).norm

lemma Tame.bdd_GD {N k : ℕ} {f : E3 → F} (h : Tame N f) (hk : k + 1 ≤ N)
    (α : Fin k → Fin 3) : ∃ C, ∀ x, GD k α f x ≤ C := by
  choose C hC using fun i : Fin 3 => h.bdd (k + 1) hk (Fin.cons i α)
  exact ⟨∑ i, C i, fun x => Finset.sum_le_sum fun i _ => hC i x⟩

lemma Tame.continuous_GD {N k : ℕ} {f : E3 → F} (h : Tame N f) (hk : k + 1 ≤ N)
    (α : Fin k → Fin 3) : Continuous (GD k α f) :=
  continuous_finset_sum _ fun _ _ => (continuous_WD h.smooth hk _).norm

lemma Tame.mono {N N' : ℕ} {f : E3 → F} (h : Tame N f) (hN : N' ≤ N) : Tame N' f :=
  ⟨h.smooth.of_le (by exact_mod_cast hN), fun k hk => h.memLp k (hk.trans hN),
    fun k hk => h.bdd k (hk.trans hN)⟩

lemma WD_zero (α : Fin 0 → Fin 3) (f : E3 → F) (x : E3) : WD 0 α f x = f x := by
  simp [WD]

lemma Tame.bdd0 {N : ℕ} {f : E3 → F} (h : Tame N f) : ∃ C, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := h.bdd 0 (Nat.zero_le _) Fin.elim0
  exact ⟨C, (norm_nonneg _).trans ((WD_zero _ f 0).symm ▸ hC 0), fun x => by
    simpa [WD_zero] using hC x⟩

lemma Tame.memLp0 {N : ℕ} {f : E3 → F} (h : Tame N f) : MemLp f 2 := by
  have := h.memLp 0 (Nat.zero_le _) Fin.elim0
  exact this.ae_eq (Eventually.of_forall fun x => WD_zero _ f x)

/-! ## Integrability toolkit -/

lemma int_of_le {G : Type*} [NormedAddCommGroup G] {h : E3 → G} {a b : E3 → ℝ}
    (hh : AEStronglyMeasurable h) (ha : MemLp a 2) (hb : MemLp b 2) (C : ℝ)
    (hle : ∀ x, ‖h x‖ ≤ C * (a x * b x)) : Integrable h :=
  ((ha.integrable_mul hb).const_mul C).mono' hh (Eventually.of_forall hle)

lemma norm_fderiv_smul_le {φ : E3 → ℝ} {g : E3 → E3} {x : E3} (hφ : DifferentiableAt ℝ φ x)
    (hg : DifferentiableAt ℝ g x) :
    ‖fderiv ℝ (fun y => φ y • g y) x‖ ≤ |φ x| * ‖fderiv ℝ g x‖ + ‖fderiv ℝ φ x‖ * ‖g x‖ := by
  rw [show (fun y => φ y • g y) = φ • g from rfl,
    (hφ.hasFDerivAt.smul hg.hasFDerivAt).fderiv]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs]
  · rw [ContinuousLinearMap.norm_smulRight_apply]

lemma hasFDerivAt_halfNormSq {g : E3 → E3} {x : E3} (hg : DifferentiableAt ℝ g x) :
    HasFDerivAt (fun y => (1 / 2 : ℝ) * ‖g y‖ ^ 2)
      ((innerSL ℝ (g x)).comp (fderiv ℝ g x)) x := by
  have h := (hg.hasFDerivAt.norm_sq).const_mul (1 / 2 : ℝ)
  convert h using 1
  ext v
  simp

lemma norm_fderiv_halfNormSq_le {g : E3 → E3} {x : E3} (hg : DifferentiableAt ℝ g x) :
    ‖fderiv ℝ (fun y => (1 / 2 : ℝ) * ‖g y‖ ^ 2) x‖ ≤ ‖g x‖ * ‖fderiv ℝ g x‖ := by
  rw [(hasFDerivAt_halfNormSq hg).fderiv]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  rw [innerSL_apply_norm]

lemma norm_gradient_eq (φ : E3 → ℝ) (x : E3) : ‖gradient φ x‖ = ‖fderiv ℝ φ x‖ := by
  unfold gradient
  exact LinearIsometryEquiv.norm_map _ _

lemma abs_div_le (G : VelocityField) (x : E3) (hG : DifferentiableAt ℝ G x) :
    |div G x| ≤ 3 * ‖fderiv ℝ G x‖ := by
  unfold div
  have h : ∀ j : Fin 3, |fderiv ℝ (fun y => G y j) x (e j)| ≤ ‖fderiv ℝ G x‖ := fun j => by
    rw [MildEnergyIneq.fderiv_coord hG]
    calc |fderiv ℝ G x (e j) j| ≤ ‖fderiv ℝ G x (e j)‖ := by
          simpa using PiLp.norm_apply_le (fderiv ℝ G x (e j)) j
      _ ≤ ‖fderiv ℝ G x‖ * ‖e j‖ := (fderiv ℝ G x).le_opNorm _
      _ = ‖fderiv ℝ G x‖ := by simp [e]
  calc |∑ j : Fin 3, fderiv ℝ (fun y => G y j) x (e j)|
      ≤ ∑ j : Fin 3, |fderiv ℝ (fun y => G y j) x (e j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 3, ‖fderiv ℝ G x‖ := Finset.sum_le_sum fun j _ => h j
    _ = 3 * ‖fderiv ℝ G x‖ := by simp

lemma continuous_div {G : VelocityField} (hG : ContDiff ℝ 1 G) : Continuous (div G) := by
  unfold div
  refine continuous_finset_sum _ fun j _ => ?_
  have hc : ContDiff ℝ 1 (fun y => G y j) :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hG
  exact (hc.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- Flux vanishing from a pointwise bound on the derivative. -/
lemma integral_div_eq_zero_of_le {G : VelocityField} (hG : ContDiff ℝ 1 G)
    (hG1 : Integrable G) {g : E3 → ℝ} (hg : Integrable g)
    (hle : ∀ x, ‖fderiv ℝ G x‖ ≤ g x) : ∫ x, div G x = 0 := by
  refine DivergenceWholeSpace.integral_div_eq_zero G hG hG1 ?_
  refine (hg.const_mul 3).mono' (continuous_div hG).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact (abs_div_le G x (hG.differentiable one_ne_zero x)).trans
    (mul_le_mul_of_nonneg_left (hle x) (by norm_num))

/-! ## `WordIBP` from tameness -/

open KatoPonce KatoPonceHypotheses

section WordIBP

variable {u : VelocityField} {p : PressureField} (hu : ContDiff ℝ ∞ u) (hp : ContDiff ℝ ∞ p)
  (hdiv : ∀ x, div u x = 0) (tu : Tame 5 u) (tp : Tame 4 p) (tc : Tame 3 (convective u u))

include hu hp hdiv tu tp tc in
/-- **`WordIBP` at one word**, `|α| ≤ 3`, from tameness of `u`, `p`, `(u·∇)u`. -/
theorem wordIBP_of_tame {k : ℕ} (hk : k ≤ 3) (α : Fin k → Fin 3) : WordIBP u p k α := by
  obtain ⟨Cu, hCu0, hCu⟩ := tu.bdd0
  set w := wordDeriv k α u with hw
  set q := wordDerivScalar k α p with hq
  have hwWD : w = WD k α u := rfl
  have hqWD : q = WD k α p := rfl
  have hwC : ContDiff ℝ ∞ w := contDiff_wordDeriv α hu
  have hqC : ContDiff ℝ ∞ q := by
    unfold q
    exact KatoPonceHypotheses.contDiff_wordDerivScalar α hp
  have hwd : ∀ x, DifferentiableAt ℝ w x := fun x => hwC.differentiable (by simp) x
  have hqd : ∀ x, DifferentiableAt ℝ q x := fun x => hqC.differentiable (by simp) x
  have hud : ∀ x, DifferentiableAt ℝ u x := fun x => hu.differentiable (by simp) x
  have hwL : MemLp w 2 := tu.memLp k (by omega) α
  have hqL : MemLp q 2 := tp.memLp k (by omega) α
  have hwn : MemLp (fun x => ‖w x‖) 2 := hwL.norm
  have hqn : MemLp (fun x => ‖q x‖) 2 := hqL.norm
  have hGw : MemLp (GD k α u) 2 := tu.memLp_GD (by omega) α
  have hGq : MemLp (GD k α p) 2 := tp.memLp_GD (by omega) α
  have hGu : MemLp (GD 0 Fin.elim0 u) 2 := tu.memLp_GD (by omega) Fin.elim0
  have hDw : ∀ x, ‖fderiv ℝ w x‖ ≤ GD k α u x := norm_fderiv_WD_le tu.smooth (by omega) α
  have hDq : ∀ x, ‖fderiv ℝ q x‖ ≤ GD k α p x := norm_fderiv_WD_le tp.smooth (by omega) α
  have hDu : ∀ x, ‖fderiv ℝ u x‖ ≤ GD 0 Fin.elim0 u x := by
    intro x
    have h := norm_fderiv_WD_le tu.smooth (by omega : 0 + 1 ≤ 5) Fin.elim0 x
    have he : WD 0 Fin.elim0 u = u := funext fun y => WD_zero _ u y
    rwa [he] at h
  obtain ⟨Cw, hCw⟩ := tu.bdd k (by omega) α
  have hcu : Continuous u := hu.continuous
  have hcw : Continuous w := hwC.continuous
  have hcq : Continuous q := hqC.continuous
  have hcDw : Continuous (fderiv ℝ w) := hwC.continuous_fderiv (by simp)
  have hcDq : Continuous (fderiv ℝ q) := hqC.continuous_fderiv (by simp)
  set φ : E3 → ℝ := fun y => (1 / 2 : ℝ) * ‖w y‖ ^ 2 with hφ
  have hφC : ContDiff ℝ ∞ φ := contDiff_const.mul (hwC.norm_sq ℝ)
  have hcDφ : Continuous (fderiv ℝ φ) := hφC.continuous_fderiv (by simp)
  have hDφ : ∀ x, ‖fderiv ℝ φ x‖ ≤ ‖w x‖ * GD k α u x := fun x =>
    (norm_fderiv_halfNormSq_le (hwd x)).trans (mul_le_mul_of_nonneg_left (hDw x) (norm_nonneg _))
  have hcgrad : ∀ {ψ : E3 → ℝ}, Continuous (fderiv ℝ ψ) → Continuous (gradient ψ) := by
    intro ψ h
    exact (InnerProductSpace.toDual ℝ E3).symm.continuous.comp h
  have hφabs : ∀ x, |φ x| = (1 / 2) * (‖w x‖ * ‖w x‖) := fun x => by
    rw [abs_of_nonneg (by positivity)]; ring
  -- the pressure pair
  have hpp : Integrable (fun x => inner ℝ (w x) (gradient q x)) := by
    refine int_of_le ((hcw.inner (hcgrad hcDq))).aestronglyMeasurable hwn hGq 1 fun x => ?_
    rw [Real.norm_eq_abs, one_mul]
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [norm_gradient_eq]
    exact mul_le_mul_of_nonneg_left (hDq x) (norm_nonneg _)
  -- the transport pair
  have htp : Integrable (fun x => inner ℝ (w x) (convective u w x)) := by
    refine int_of_le (hcw.inner ((hcDw.clm_apply hcu))).aestronglyMeasurable hwn hGw Cu
      fun x => ?_
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖w x‖ * ‖convective u w x‖ ≤ ‖w x‖ * (GD k α u x * Cu) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact ((fderiv ℝ w x).le_opNorm _).trans
            (mul_le_mul (hDw x) (hCu x) (norm_nonneg _) ((norm_nonneg _).trans (hDw x)))
      _ = Cu * (‖w x‖ * GD k α u x) := by ring
  -- the second word partials and the viscous package
  have hW1 : ∀ i : Fin 3, (fun y => fderiv ℝ w y (e i)) = WD (k + 1) (Fin.cons i α) u :=
    fun i => funext fun y => fderiv_WD tu.smooth (by omega) α i y
  have hW2 : ∀ i : Fin 3, ∀ y, fderiv ℝ (WD (k + 1) (Fin.cons i α) u) y (e i) =
      WD (k + 2) (Fin.cons i (Fin.cons i α)) u y :=
    fun i y => fderiv_WD tu.smooth (by omega) _ i y
  have hL1 : ∀ i : Fin 3, MemLp (WD (k + 1) (Fin.cons i α) u) 2 :=
    fun i => tu.memLp (k + 1) (by omega) _
  have hL2 : ∀ i : Fin 3, MemLp (WD (k + 2) (Fin.cons i (Fin.cons i α)) u) 2 :=
    fun i => tu.memLp (k + 2) (by omega) _
  have hc1 : ∀ i : Fin 3, Continuous (WD (k + 1) (Fin.cons i α) u) :=
    fun i => continuous_WD tu.smooth (by omega) _
  have hc2 : ∀ i : Fin 3, Continuous (WD (k + 2) (Fin.cons i (Fin.cons i α)) u) :=
    fun i => continuous_WD tu.smooth (by omega) _
  have hd1 : ∀ i : Fin 3, Differentiable ℝ (WD (k + 1) (Fin.cons i α) u) :=
    fun i => differentiable_WD tu.smooth (by omega) _
  have hlap : ∀ x, laplacian w x = ∑ i : Fin 3, WD (k + 2) (Fin.cons i (Fin.cons i α)) u x := by
    intro x
    unfold laplacian
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hW1 i, hW2 i x]
  have hS : MemLp (fun x => ∑ i : Fin 3, ‖WD (k + 2) (Fin.cons i (Fin.cons i α)) u x‖) 2 :=
    memLp_finset_sum _ fun i _ => (hL2 i).norm
  have hvisc : Integrable (fun x => inner ℝ (w x) (laplacian w x)) := by
    refine int_of_le ?_ hwn hS 1 fun x => ?_
    · simp only [hlap]
      exact (hcw.inner (continuous_finset_sum _ fun i _ => hc2 i)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, one_mul, hlap]
      refine (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _))
  have hcoordL : ∀ {g : E3 → E3}, MemLp g 2 → ∀ j : Fin 3, MemLp (fun y => g y j) 2 :=
    fun hg j => (EuclideanSpace.proj (𝕜 := ℝ) j).comp_memLp' hg
  have hcoordle : ∀ (v : E3) (j : Fin 3), |v j| ≤ ‖v‖ := fun v j => by
    simpa using PiLp.norm_apply_le v j
  have hpibp : ∀ i j : Fin 3, PartialIBP i (fun y => w y j) (fun y => directionalCoord w j i y) := by
    intro i j
    have hψ : (fun y => directionalCoord w j i y) = fun y => WD (k + 1) (Fin.cons i α) u y j := by
      funext y
      unfold directionalCoord
      rw [MildEnergyIneq.fderiv_coord (hwd y)]
      exact congrArg (fun v : E3 => v j) (congrFun (hW1 i) y)
    have hdφ : ∀ y, fderiv ℝ (fun y => w y j) y (e i) = WD (k + 1) (Fin.cons i α) u y j :=
      fun y => by rw [MildEnergyIneq.fderiv_coord (hwd y)]; exact congrArg (fun v : E3 => v j) (congrFun (hW1 i) y)
    have hdψ : ∀ y, fderiv ℝ (fun y => WD (k + 1) (Fin.cons i α) u y j) y (e i) =
        WD (k + 2) (Fin.cons i (Fin.cons i α)) u y j := fun y => by
      rw [MildEnergyIneq.fderiv_coord (hd1 i y)]
      exact congrArg (fun v : E3 => v j) (hW2 i y)
    have hcj : ∀ {g : E3 → E3}, Continuous g → Continuous fun y => g y j := fun hg =>
      (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp hg
    have hdj : ∀ {g : E3 → E3}, Differentiable ℝ g → ∀ y, DifferentiableAt ℝ (fun y => g y j) y :=
      fun hg y => ((EuclideanSpace.proj (𝕜 := ℝ) j).differentiableAt).comp y (hg y)
    have hIl : Integrable (fun x => w x j * WD (k + 2) (Fin.cons i (Fin.cons i α)) u x j) :=
      (hcoordL hwL j).integrable_mul (hcoordL (hL2 i) j)
    have hIr : Integrable (fun x => WD (k + 1) (Fin.cons i α) u x j *
        WD (k + 1) (Fin.cons i α) u x j) :=
      (hcoordL (hL1 i) j).integrable_mul (hcoordL (hL1 i) j)
    rw [hψ]
    refine ⟨fun y => hdj (fun y => hwd y) y, hdj (hd1 i), ?_, ?_, ?_⟩
    · simp only [hdψ]; exact hIl
    · simp only [hdφ]; exact hIr
    · set G : VelocityField := fun y =>
        (w y j * WD (k + 1) (Fin.cons i α) u y j) • EuclideanSpace.single i (1 : ℝ)
      have hGC : ContDiff ℝ 1 G := by
        let ψ : E3 → ℝ := fun y => w y j * WD (k + 1) (Fin.cons i α) u y j
        have hψC : ContDiff ℝ 1 ψ :=
          ContDiff.mul
            ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp (hwC.of_le (by exact_mod_cast le_top)))
            ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp
              (contDiff_WD tu.smooth (by omega : 1 + (k + 1) ≤ 5) _))
        change ContDiff ℝ 1 (fun y => ψ y • EuclideanSpace.single i (1 : ℝ))
        exact hψC.smul contDiff_const
      refine DivergenceWholeSpace.integral_div_eq_zero G hGC ?_ ?_
      · refine int_of_le (((hcj hcw).mul (hcj (hc1 i))).smul continuous_const).aestronglyMeasurable
          (hcoordL hwL j).norm (hcoordL (hL1 i) j).norm 1 fun x => ?_
        simp [G, norm_smul]
      · have h := fun x => div_mul_smul_single (fun y => w y j)
          (fun y => WD (k + 1) (Fin.cons i α) u y j) i x (hdj (fun y => hwd y) x) (hdj (hd1 i) x)
        simp only [hdψ, hdφ] at h
        have hfun : div G = fun x => w x j * WD (k + 2) (Fin.cons i (Fin.cons i α)) u x j +
            WD (k + 1) (Fin.cons i α) u x j * WD (k + 1) (Fin.cons i α) u x j := funext h
        rw [hfun]
        exact hIl.add hIr
  have hviscIBP : ViscousDissipationIBP w := ⟨contDiff_of_infty hwC, hpibp, hvisc⟩
  -- the convective term
  have hconv : Integrable (fun x => inner ℝ (w x) (wordDeriv k α (convective u u) x)) := by
    obtain ⟨Cc, -⟩ := tc.bdd k hk α
    refine int_of_le (hcw.inner (continuous_WD tc.smooth hk α)).aestronglyMeasurable hwn
      (tc.memLp k hk α).norm 1 fun x => ?_
    rw [Real.norm_eq_abs, one_mul]
    exact abs_real_inner_le_norm _ _
  refine
    { integrable_transport_pair := ?_
      integrable_transport_div := ?_
      flux_transport := ?_
      integrable_pressure_pair := hpp
      integrable_pressure_div := ?_
      flux_pressure := ?_
      viscous := hviscIBP
      integrable_viscous := hvisc
      integrable_transport := htp
      integrable_commutator := ?_
      integrable_convective := hconv
      integrable_pressure := ?_
      integrable_laplacian := ?_ }
  · refine int_of_le (hcu.inner (hcgrad hcDφ)).aestronglyMeasurable hwn hGw Cu fun x => ?_
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [norm_gradient_eq]
    calc ‖u x‖ * ‖fderiv ℝ φ x‖ ≤ Cu * (‖w x‖ * GD k α u x) :=
          mul_le_mul (hCu x) (hDφ x) (norm_nonneg _) hCu0
      _ = _ := rfl
  · simp only [hdiv, zero_mul]; exact integrable_zero _ _ _
  · refine integral_div_eq_zero_of_le ((hφC.smul hu).of_le (by simp)) ?_
      (((hwn.integrable_mul hGu).const_mul ((1 / 2) * Cw)).add
        ((hwn.integrable_mul hGw).const_mul Cu)) fun x => ?_
    · refine int_of_le (hφC.continuous.smul hcu).aestronglyMeasurable hwn hwn ((1 / 2) * Cu)
        fun x => ?_
      rw [norm_smul, Real.norm_eq_abs, hφabs]
      have := hCu x
      nlinarith [norm_nonneg (w x), norm_nonneg (u x), mul_nonneg (norm_nonneg (w x)) (norm_nonneg (w x))]
    · refine (norm_fderiv_smul_le (hφC.differentiable (by simp) x) (hud x)).trans ?_
      rw [hφabs]
      have h1 := hDu x; have h2 := hDφ x; have h3 := hCu x
      have hCw0 : 0 ≤ Cw := (norm_nonneg _).trans (hCw 0)
      have hwCw : ‖w x‖ ≤ Cw := hCw x
      have h5 : 0 ≤ GD 0 Fin.elim0 u x := (norm_nonneg _).trans h1
      have h6 : 0 ≤ GD k α u x := (norm_nonneg _).trans (hDw x)
      have h7 := norm_nonneg (w x)
      have h9 := norm_nonneg (fderiv ℝ u x)
      have h10 := norm_nonneg (u x)
      calc (1 / 2) * (‖w x‖ * ‖w x‖) * ‖fderiv ℝ u x‖ + ‖fderiv ℝ φ x‖ * ‖u x‖
          ≤ (1 / 2) * (‖w x‖ * Cw) * GD 0 Fin.elim0 u x + (‖w x‖ * GD k α u x) * Cu := by
            refine add_le_add ?_ ?_
            · refine mul_le_mul ?_ h1 h9 (mul_nonneg (by norm_num) (mul_nonneg h7 hCw0))
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwCw h7) (by norm_num)
            · exact mul_le_mul h2 h3 h10 (mul_nonneg h7 h6)
        _ = (1 / 2) * Cw * (‖w x‖ * GD 0 Fin.elim0 u x) + Cu * (‖w x‖ * GD k α u x) := by ring
  · simp only [div_wordDeriv_eq α hu hdiv, zero_mul]; exact integrable_zero _ _ _
  · refine integral_div_eq_zero_of_le ((hqC.smul hwC).of_le (by simp)) ?_
      ((hqn.integrable_mul hGw).add (hGq.integrable_mul hwn)) fun x => ?_
    · refine int_of_le (hcq.smul hcw).aestronglyMeasurable hqn hwn 1 fun x => ?_
      rw [norm_smul, one_mul]
    · refine (norm_fderiv_smul_le (hqd x) (hwd x)).trans ?_
      rw [← Real.norm_eq_abs]
      exact add_le_add (mul_le_mul_of_nonneg_left (hDw x) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (hDq x) (norm_nonneg _))
  · have h := hconv.sub htp
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply, convectiveCommutator, inner_sub_right, hw]
  · rw [wordDeriv_pressureGradient_eq α hp]
    exact hpp
  · rw [wordDeriv_laplacian_eq α hu]
    exact hvisc

include hu hp hdiv tu tp tc in
theorem h3IBPVanishingFlux_of_tame : H3IBPVanishingFlux u p := fun k hk α =>
  wordIBP_of_tame hu hp hdiv tu tp tc (by have := Finset.mem_range.1 hk; omega) α

end WordIBP

/-! ## Tameness of physical fields of `Ĥ^m` slices -/

open LerayHeat SobolevFourier SobolevHilbert InverseSobolev LerayPressure FourierInvBCF
  FeffermanMild MildEnergy

lemma WD_comp_clm {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {N k : ℕ}
    {g : E3 → G} (hg : ContDiff ℝ N g) (hk : k ≤ N) (L : G →L[ℝ] F) (α : Fin k → Fin 3)
    (x : E3) : WD k α (fun y => L (g y)) x = L (WD k α g x) := by
  unfold WD
  rw [show (fun y => L (g y)) = L ∘ g from rfl,
    L.iteratedFDeriv_comp_left (hg.of_le (by exact_mod_cast hk)).contDiffAt le_rfl]
  rfl

theorem tame_physicalOfHm {N m : ℕ} (hm : N + 2 ≤ m) (A : Hm m) : Tame N (physicalOfHm A) := by
  have hsm : ContDiff ℝ N (physicalOfHm A) := contDiff_physicalOfHm hm A
  have key : ∀ k ≤ N, ∀ α : Fin k → Fin 3, ∃ (n : ℕ) (hn : 2 ≤ n) (A' : Hm n),
      WD k α (physicalOfHm A) = fun x => realify (fourierInvBCF hn A' x) := by
    intro k hk α
    obtain ⟨n, hn, A', -, -, hdw⟩ := dw_fourierInvBCF k (by omega : k + 2 ≤ m) A α
    refine ⟨n, hn, A', funext fun x => ?_⟩
    have h := wordDeriv_physicalOfHm (by omega : k + 2 ≤ m) A α x
    refine h.trans ?_
    rw [hdw]
  refine ⟨hsm, fun k hk α => ?_, fun k hk α => ?_⟩
  · obtain ⟨n, hn, A', hA'⟩ := key k hk α
    refine (PlancherelBridge.memLp_fourierInvBCF hn A').of_le
      (continuous_WD hsm hk α).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [hA']
    exact norm_realify_le _
  · obtain ⟨n, hn, A', hA'⟩ := key k hk α
    exact ⟨‖fourierInvBCF hn A'‖, fun x => by
      rw [hA']
      exact (norm_realify_le _).trans ((fourierInvBCF hn A').norm_coe_le_norm x)⟩

/-- The scalar read-off `v ↦ Re v₀`. -/
def re0 : V →L[ℝ] ℝ := Complex.reCLM.comp coord0ℝ

lemma norm_re0_le (v : V) : ‖re0 v‖ ≤ ‖v‖ := by
  simp only [re0, ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm _).trans (PiLp.norm_apply_le v 0)

theorem tame_lerayPressure {N s : ℕ} (hs : 3 ≤ s) (hN : N + 2 ≤ s) (U : Hm s) :
    Tame N (lerayPressure hs U) := by
  set P := lerayPressureHm hs U
  have hp : lerayPressure hs U = fun x => re0 (fourierInvBCF (by omega : 2 ≤ s) P x) := by
    funext x
    unfold lerayPressure
    rw [physicalInv_def]
    rfl
  have hg : ContDiff ℝ N (fourierInvBCF (by omega : 2 ≤ s) P : E3 → V) :=
    contDiff_fourierInv_of_Hm hN P
  have key : ∀ k ≤ N, ∀ α : Fin k → Fin 3, ∃ (n : ℕ) (hn : 2 ≤ n) (A' : Hm n),
      WD k α (lerayPressure hs U) = fun x => re0 (fourierInvBCF hn A' x) := by
    intro k hk α
    obtain ⟨n, hn, A', -, -, hdw⟩ := dw_fourierInvBCF k (by omega : k + 2 ≤ s) P α
    refine ⟨n, hn, A', funext fun x => ?_⟩
    rw [hp, WD_comp_clm hg hk]
    exact congrArg re0 (congrFun hdw x)
  have hsm : ContDiff ℝ N (lerayPressure hs U) := contDiff_lerayPressure hs hN U
  refine ⟨hsm, fun k hk α => ?_, fun k hk α => ?_⟩
  · obtain ⟨n, hn, A', hA'⟩ := key k hk α
    refine (PlancherelBridge.memLp_fourierInvBCF hn A').of_le
      (continuous_WD hsm hk α).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [hA']
    exact norm_re0_le _
  · obtain ⟨n, hn, A', hA'⟩ := key k hk α
    exact ⟨‖fourierInvBCF hn A'‖, fun x => by
      rw [hA']
      exact (norm_re0_le _).trans ((fourierInvBCF hn A').norm_coe_le_norm x)⟩

/-! ## Along the realized mild solution -/

section MildPath

open MildTimeDeriv MildPathSmooth RepairedTether MildReal MildMomentum PersistenceHm
  NonlinearHm MildPressureSmooth

variable {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀) (hdec : FeffermanDecay u₀)
  {ν : ℝ} (hν : 0 < ν)

lemma physicalMild_eq_IccExtend {k : ℕ} (hk : 2 ≤ k) (t : ℝ) :
    physicalMild hf hdec hν t = physicalOfHm
      (ContinuousMap.IccExtend (Tfeff_nonneg hf hdec hν) (persistPath hf hdec hν hk) t) := by
  rw [physicalMild_eq_inclExt hf hdec hν hk (le_refl (k + 1)) t]
  unfold inclExt
  rw [incl_self_Hm]

lemma contDiff_physicalMild_slice (t : ℝ) : ContDiff ℝ ∞ (physicalMild hf hdec hν t) := by
  refine contDiff_infty.2 fun n => ?_
  rw [physicalMild_eq_IccExtend hf hdec hν (by omega : 2 ≤ n + 2) t]
  exact contDiff_physicalOfHm (by omega) _

lemma contDiff_presMild_slice (t : ℝ) : ContDiff ℝ ∞ (presMild hf hdec hν t) := by
  refine contDiff_infty.2 fun n => ?_
  rw [presMild_eq_inclExt hf hdec hν (by omega : 2 ≤ n + 3) (by omega : 3 ≤ n + 3)
    (by omega : n + 3 ≤ n + 3 + 1) t]
  exact contDiff_lerayPressure _ (by omega) _

lemma lerayH_IccExtend_k (hdiv : ∀ x, div u₀ x = 0) {k : ℕ} (hk : 2 ≤ k) (t : ℝ) :
    lerayH (k + 1) (ContinuousMap.IccExtend (Tfeff_nonneg hf hdec hν)
      (persistPath hf hdec hν hk) t) =
      ContinuousMap.IccExtend (Tfeff_nonneg hf hdec hν) (persistPath hf hdec hν hk) t := by
  rw [IccExtend_persistPath_apply]
  exact MildDivFree.lerayH_mildS hk (Tfeff_nonneg hf hdec hν) hν
    (MildDivFree.lerayH_toHmFeff hf hdec hdiv (k + 1)) (persistPath_mildS hf hdec hν hk) _

lemma im_IccExtend_k {k : ℕ} (hk : 2 ≤ k) (t : ℝ) (y : E3) (i : Fin 3) :
    (FourierTransformInv.fourierInv ((ContinuousMap.IccExtend (Tfeff_nonneg hf hdec hν)
      (persistPath hf hdec hν hk) t : Hm (k + 1)) : E3 → V) y i).im = 0 := by
  rw [IccExtend_persistPath_apply]
  exact fourierInv_im_eq_zero (refl_persistPath_high hf hdec hν hk _) y i

lemma convective_physicalMild (hdiv : ∀ x, div u₀ x = 0) {k : ℕ} (hk : 2 ≤ k) (t : ℝ) :
    convective (physicalMild hf hdec hν t) (physicalMild hf hdec hν t) =
      physicalOfHm (divTensor (three_le_succ hk)
        (ContinuousMap.IccExtend (Tfeff_nonneg hf hdec hν) (persistPath hf hdec hν hk) t)) := by
  funext x
  rw [physicalMild_eq_IccExtend hf hdec hν hk t]
  exact (realify_fourierInv_divTensor (three_le_succ hk) (lerayH_IccExtend_k hf hdec hν hdiv hk t)
    (im_IccExtend_k hf hdec hν hk t) x).symm

/-- **Open item 1.** Every time slice of the realized mild solution satisfies
`H3IBPVanishingFlux` with the Leray pressure. -/
theorem h3IBPVanishingFlux_physicalMild (hdiv : ∀ x, div u₀ x = 0) (t : ℝ) :
    H3IBPVanishingFlux (physicalMild hf hdec hν t) (presMild hf hdec hν t) := by
  refine h3IBPVanishingFlux_of_tame (contDiff_physicalMild_slice hf hdec hν t)
    (contDiff_presMild_slice hf hdec hν t) (MildDivFree.div_physicalMild hf hdec hdiv hν t)
    ?_ ?_ ?_
  · rw [physicalMild_eq_IccExtend hf hdec hν (by norm_num : 2 ≤ 6) t]
    exact tame_physicalOfHm (by norm_num) _
  · rw [presMild_eq_inclExt hf hdec hν (by norm_num : 2 ≤ 6) (by norm_num : 3 ≤ 7)
      (by norm_num : 7 ≤ 6 + 1) t]
    exact tame_lerayPressure _ (by norm_num) _
  · rw [convective_physicalMild hf hdec hν hdiv (by norm_num : 2 ≤ 6) t]
    exact tame_physicalOfHm (by norm_num) _

end MildPath

end MildFlux

#print axioms MildFlux.wordIBP_of_tame
#print axioms MildFlux.h3IBPVanishingFlux_of_tame
#print axioms MildFlux.tame_physicalOfHm
#print axioms MildFlux.tame_lerayPressure
#print axioms MildFlux.h3IBPVanishingFlux_physicalMild
