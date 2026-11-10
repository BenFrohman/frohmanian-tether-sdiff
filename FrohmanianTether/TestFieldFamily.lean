/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import FrohmanianTether.TetherNondegeneracy
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# A family of concentrated divergence-free test fields

For a scalar `H : ℝ³ → ℝ`, `curlVal H = curl (H e₂) = (∂₁H, -∂₀H, 0)`. If `H` is smooth with
compact support, `curlOrbit H` is a test direction (`curlOrbit_test`): smooth, compactly
supported, divergence-free (`div_curlVal`, from the symmetry of second derivatives), with
`tsupport (curlVal H) ⊆ tsupport H` (`tsupport_curlVal_subset`). The pointwise pairing is
`⟨curl(H e₂), curl(K e₂)⟩ = ∂₀H ∂₀K + ∂₁H ∂₁K` (`inner_curlVal`).

`concField x r` (for `r > 0`) is `curlOrbit` of a smooth bump of radius `r/2` centred at `x`:
a test direction with support in the ball `B(x, r)` (`tsupport_concField_subset`) that is not
identically zero (`concField_ne_zero`).
-/

open MeasureTheory NavierStokes3D ArnoldGeometric TetherNondegeneracy
open scoped InnerProductSpace ContDiff

noncomputable section

namespace TestFieldFamily

/-- Directional partial derivative `∂ᵢ H`. -/
@[expose] public def pd (H : T3 → ℝ) (i : Fin 3) (y : T3) : ℝ := fderiv ℝ H y (eb i)

/-- `curl (H e₂) = (∂₁H, -∂₀H, 0)`. -/
@[expose] public def curlVal (H : T3 → ℝ) (y : T3) : EuclideanSpace ℝ (Fin 3) :=
  pd H 1 y • eb 0 - pd H 0 y • eb 1

public theorem curlVal_apply (H : T3 → ℝ) (y : T3) (j : Fin 3) :
    curlVal H y j = if j = 0 then pd H 1 y else if j = 1 then -pd H 0 y else 0 := by
  fin_cases j <;> simp [curlVal, eb]

public theorem inner_curlVal (H K : T3 → ℝ) (y : T3) :
    inner ℝ (curlVal H y) (curlVal K y) = pd H 0 y * pd K 0 y + pd H 1 y * pd K 1 y := by
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  simp only [curlVal_apply]
  simp only [show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide, if_false, if_true]
  simp [inner]
  ring

public theorem contDiff_pd {H : T3 → ℝ} (hH : ContDiff ℝ ∞ H) (i : Fin 3) :
    ContDiff ℝ ∞ (pd H i) :=
  (hH.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

public theorem contDiff_curlVal {H : T3 → ℝ} (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ (curlVal H) :=
  ((contDiff_pd hH 1).smul contDiff_const).sub ((contDiff_pd hH 0).smul contDiff_const)

/-- The map `L ↦ L e₁ • e₀ - L e₀ • e₁` sending the derivative to `curl (H e₂)`. -/
def curlMap (L : T3 →L[ℝ] ℝ) : EuclideanSpace ℝ (Fin 3) := L (eb 1) • eb 0 - L (eb 0) • eb 1

theorem curlVal_eq_comp (H : T3 → ℝ) : curlVal H = curlMap ∘ fderiv ℝ H := rfl

public theorem hasCompactSupport_curlVal {H : T3 → ℝ} (hH : HasCompactSupport H) :
    HasCompactSupport (curlVal H) := by
  rw [curlVal_eq_comp]
  exact (hH.fderiv (𝕜 := ℝ)).comp_left (by simp [curlMap])

public theorem tsupport_curlVal_subset (H : T3 → ℝ) : tsupport (curlVal H) ⊆ tsupport H := by
  rw [curlVal_eq_comp]
  exact (tsupport_comp_subset (by simp [curlMap]) _).trans (tsupport_fderiv_subset ℝ)

/-- `curl (H e₂)` is divergence-free (symmetry of second derivatives). -/
public theorem div_curlVal {H : T3 → ℝ} (hH : ContDiff ℝ ∞ H) (x : T3) :
    NavierStokes3D.div (curlVal H) x = 0 := by
  have hc : ∀ i, (fun y => curlVal H y i) =
      if i = 0 then pd H 1 else if i = 1 then fun y => -pd H 0 y else fun _ => 0 := by
    intro i; fin_cases i <;> funext y <;> simp [curlVal_apply]
  have hd : Differentiable ℝ (fderiv ℝ H) :=
    (hH.fderiv_right (m := 1) (by norm_cast)).differentiable one_ne_zero
  have hpd : ∀ i j, fderiv ℝ (pd H i) x (eb j) = fderiv ℝ (fderiv ℝ H) x (eb j) (eb i) := by
    intro i j
    have : pd H i = fun y => (fderiv ℝ H y) (eb i) := rfl
    rw [this, fderiv_clm_apply (hd x) (differentiableAt_const _)]
    simp
  have hsymm : IsSymmSndFDerivAt ℝ H x :=
    hH.contDiffAt.isSymmSndFDerivAt (by simp; exact WithTop.coe_le_coe.mpr (le_top : (2:ℕ∞) ≤ ⊤))
  simp only [NavierStokes3D.div, Fin.sum_univ_three, hc]
  simp only [show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide, if_false, if_true]
  rw [fderiv_fun_neg]
  simp only [fderiv_const_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.zero_apply]
  have e0 := hpd 1 0
  have e1 := hpd 0 1
  simp only [eb] at e0 e1 ⊢
  rw [e0, e1, hsymm]
  ring

/-- The test direction `curl (H e₂)`. -/
@[expose] public def curlOrbit (H : T3 → ℝ) (hH : ContDiff ℝ ∞ H) : CoadjointOrbit :=
  ⟨curlVal H, div_curlVal hH⟩

public theorem curlOrbit_val (H : T3 → ℝ) (hH : ContDiff ℝ ∞ H) :
    (curlOrbit H hH).val = curlVal H := rfl

public theorem curlOrbit_test {H : T3 → ℝ} (hH : ContDiff ℝ ∞ H) (hc : HasCompactSupport H) :
    IsTestDirection (curlOrbit H hH) :=
  ⟨contDiff_curlVal hH, hasCompactSupport_curlVal hc⟩

/-- The bump of radius `r/2` (equal to `1` on the ball of radius `r/4`) centred at `x`. -/
@[expose] public def concBump (x : T3) {r : ℝ} (hr : 0 < r) : ContDiffBump x :=
  ⟨r / 4, r / 2, by positivity, by linarith⟩

/-- The concentrated field at `x` of radius `r`. -/
@[expose] public def concField (x : T3) {r : ℝ} (hr : 0 < r) : CoadjointOrbit :=
  curlOrbit (concBump x hr) (concBump x hr).contDiff

public theorem concField_test (x : T3) {r : ℝ} (hr : 0 < r) : IsTestDirection (concField x hr) :=
  curlOrbit_test _ (concBump x hr).hasCompactSupport

public theorem tsupport_concField_subset (x : T3) {r : ℝ} (hr : 0 < r) :
    tsupport (concField x hr).val ⊆ Metric.ball x r := by
  refine (tsupport_curlVal_subset _).trans ?_
  rw [ContDiffBump.tsupport_eq]
  exact Metric.closedBall_subset_ball (by simp [concBump]; linarith)

/-- The concentrated field is not identically zero. -/
public theorem concField_ne_zero (x : T3) {r : ℝ} (hr : 0 < r) :
    ∃ y, (concField x hr).val y ≠ 0 := by
  by_contra hall
  push Not at hall
  set f := concBump x hr
  set F : T3 → ℝ := ⇑f with hF
  have h0 : ∀ y, pd f 0 y = 0 := by
    intro y
    have := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) (hall y)
    simpa [concField, curlOrbit, curlVal_apply] using this
  set φ : ℝ → ℝ := fun t => F (x + t • eb 0)
  have hφd : ∀ t, HasDerivAt φ (pd f 0 (x + t • eb 0)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x + t • eb 0) (eb 0) t := by
      simpa using ((hasDerivAt_id t).smul_const (eb 0)).const_add x
    have h2 : HasFDerivAt F (fderiv ℝ F (x + t • eb 0)) (x + t • eb 0) :=
      ((f.contDiff (n := 1)).differentiable one_ne_zero (x + t • eb 0)).hasFDerivAt
    exact HasFDerivAt.comp_hasDerivAt (l := F) (f := fun t : ℝ => x + t • eb 0) t h2 h1
  have hconst : φ 0 = φ r := by
    have hdiff : Differentiable ℝ φ := fun t => (hφd t).differentiableAt
    exact is_const_of_deriv_eq_zero hdiff (fun t => by rw [(hφd t).deriv, h0]) 0 r
  have hA : φ 0 = 1 := by
    simp only [φ, zero_smul, add_zero]
    exact f.one_of_mem_closedBall (Metric.mem_closedBall_self (by simp [f, concBump]; positivity))
  have hB : φ r = 0 := by
    simp only [φ]
    apply f.zero_of_le_dist
    have hn : ‖eb 0‖ = 1 := by simp [eb]
    have : dist (x + r • eb 0) x = r := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hn, Real.norm_eq_abs,
        abs_of_pos hr, mul_one]
    rw [this]; simp [f, concBump]; linarith
  rw [hA, hB] at hconst
  exact one_ne_zero hconst

end TestFieldFamily

end
