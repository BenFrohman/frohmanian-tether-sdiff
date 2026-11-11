/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import BKMPillar.FeffermanClayNS.FeffermanStatements

open scoped BigOperators Gradient Topology
open ENNReal InnerProductSpace MeasureTheory Finset Filter
open FeffermanNavierStokes3D

/-!
# Compact Torus Exclusion of Global Linear Background Strain & Biot–Savart Direction Depletion

This module proves three structural facts on the periodic 3-torus `𝕋³ = ℝ³ / ℤ³`
(Fefferman's Equation (8), `IsZ3Periodic`):

1. **Exclusion of Global Linear Background Strain (`z3_periodic_linear_eq_zero`,
   `burgers_background_strain_not_z3_periodic`, `burgersLinearStrain_not_z3_periodic`):**
   Every `ℤ³`-periodic linear map `L : T3 →ₗ[ℝ] E` (or continuous linear map `L : T3 →L[ℝ] E`)
   vanishes identically (`L = 0`), and the classical global Burgers linear background strain
   `u_ext(x) = (-α x₀ / 2, -α x₁ / 2, α x₂)` with `α ≠ 0` (which is divergence-free on `ℝ³`,
   `burgersLinearStrain_div_zero`) violates `IsZ3Periodic`.
   *Mathematical scope note:* Periodicity rules out only a **global** linear background strain on
   `ℝ³ / ℤ³`; localized Burgers-like stretched vortex tubes can still form inside a periodic cell,
   so excluding global linear strain does **not** by itself resolve `Clay_B_exact`.

2. **Biot–Savart Determinant Alignment Depletion (`biot_savart_det_aligned_eq_zero`,
   `aligned_vorticity_stretching_integrand_zero`, `biot_savart_det_difference_identity`):**
   In the 3D Biot–Savart singular integral kernel for vortex stretching, the scalar triple product
   `det3 yhat (ω(x + y)) ξ(x)` vanishes identically whenever `ω(x + y) = ‖ω(x + y)‖ • ξ(x)` is
   aligned with `ξ(x)`, and satisfies the exact direction-difference identity
   `det3 yhat (mag • ξy) ξx = mag * det3 yhat (ξy - ξx) ξx`.

3. **Navier–Stokes `λ⁶` Scaling Homogeneity (`navier_stokes_scaling_homogeneity_deg6`):**
   Under the Navier–Stokes parabolic rescaling `u_λ(x, t) = λ u(λ x, λ² t)`, vorticity scales as
   `M_λ = λ² M`, so `∂_t M` and the Calderón–Zygmund stretching bound `C_CZ M³` both scale with
   degree `λ⁶` (`(λ²)³ = λ⁶`). A scale-consistent high-set damping term `-κ_eff M³` (where
   `κ_eff = κ₀ / M` absorbs one power of `M`) matches the `λ⁶` homogeneity of the unmodified
   vorticity equation, whereas an unnormalized quartic `-κ M⁴` scales as `λ⁸`.
-/

namespace FeffermanClayNS

/-- Any `ℤ³`-periodic function `f : T3 → α` is invariant under unit coordinate shifts `eⱼ`. -/
public theorem z3_periodic_unit_shift {α : Type*} {f : T3 → α}
    (hf : IsZ3Periodic f) (x : T3) (j : Fin 3) :
    f (x + stdBasisVec j) = f x :=
  (isZ3Periodic_iff_unit_shifts f).mp hf x j

/-- For any `ℤ³`-periodic function `f : T3 → E` into an additive group `E`, the unit-period
difference along each coordinate axis vanishes: `f (x + eⱼ) - f x = 0`. -/
public theorem z3_periodic_coord_diff_zero {E : Type*} [AddCommGroup E]
    {f : T3 → E} (hf : IsZ3Periodic f) (x : T3) (j : Fin 3) :
    f (x + stdBasisVec j) - f x = 0 := by
  rw [z3_periodic_unit_shift hf x j, sub_self]

/-- **Mean Directional Derivative Zero across a Unit Period (`[0, 1]`):**
By the Fundamental Theorem of Calculus along the coordinate segment `s ↦ x + s • eⱼ`, if `g` is
the directional derivative of a `ℤ³`-periodic function `f` and is interval-integrable on `[0, 1]`,
then `∫ s in 0..1, g s = 0`. -/
public theorem z3_periodic_deriv_integral_unit_interval_zero
    {f : T3 → ℝ} {g : ℝ → ℝ} (hf : IsZ3Periodic f) (x : T3) (j : Fin 3)
    (hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun τ : ℝ => f (x + τ • stdBasisVec j)) (g s) s)
    (hint : IntervalIntegrable g MeasureTheory.volume 0 1) :
    ∫ s in (0 : ℝ)..1, g s = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [one_smul, zero_smul, add_zero]
  exact z3_periodic_coord_diff_zero hf x j

/-- Standard basis expansion of any vector `x ∈ T3 = EuclideanSpace ℝ (Fin 3)`. -/
public theorem t3_eq_sum_stdBasisVec (x : T3) :
    x = ∑ j : Fin 3, (x j) • stdBasisVec j := by
  ext i
  unfold stdBasisVec
  rw [Fin.sum_univ_three]
  fin_cases i <;> simp

/-- **Global Linear Map Exclusion on `𝕋³ = ℝ³ / ℤ³` (`z3_periodic_linear_eq_zero`):**
Every `ℝ`-linear map `L : T3 →ₗ[ℝ] E` that is `ℤ³`-periodic (`IsZ3Periodic L`) is identically zero. -/
public theorem z3_periodic_linear_eq_zero {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L : T3 →ₗ[ℝ] E) (hper : IsZ3Periodic (fun x => L x)) :
    L = 0 := by
  ext x
  have hbasis : ∀ j : Fin 3, L (stdBasisVec j) = 0 := by
    intro j
    have h1 := z3_periodic_unit_shift hper 0 j
    simp only [zero_add, map_zero] at h1
    exact h1
  conv_lhs => rw [t3_eq_sum_stdBasisVec x]
  rw [map_sum]
  simp [map_smul, hbasis]

/-- **Continuous Linear Map Exclusion on `𝕋³ = ℝ³ / ℤ³`:**
Every continuous linear map `L : T3 →L[ℝ] E` that is `ℤ³`-periodic is identically zero. -/
public theorem z3_periodic_continuousLinear_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : T3 →L[ℝ] E) (hper : IsZ3Periodic (fun x => L x)) :
    L = 0 := by
  ext x
  have hlin : (L : T3 →ₗ[ℝ] E) = 0 :=
    z3_periodic_linear_eq_zero (L : T3 →ₗ[ℝ] E) hper
  exact LinearMap.congr_fun hlin x

/-- Any non-zero continuous linear operator `S₀ : T3 →L[ℝ] E` (`S₀ ≠ 0`) fails `IsZ3Periodic`. -/
public theorem linear_strain_not_z3_periodic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S₀ : T3 →L[ℝ] E) (hS₀ : S₀ ≠ 0) :
    ¬ IsZ3Periodic (fun x => S₀ x) := by
  intro hper
  exact hS₀ (z3_periodic_continuousLinear_eq_zero S₀ hper)

/-- **Exclusion of Global Linear Background Strain on `𝕋³ = ℝ³ / ℤ³`:**
No non-zero global linear background strain `u_ext(x) = S₀ x` (`S₀ ≠ 0`) is `ℤ³`-periodic. -/
public theorem burgers_background_strain_not_z3_periodic
    (S₀ : T3 →L[ℝ] T3) (hS₀ : S₀ ≠ 0) :
    ¬ IsZ3Periodic (fun x => S₀ x) :=
  linear_strain_not_z3_periodic S₀ hS₀

/-- Concrete global axisymmetric Burgers background strain velocity field on `ℝ³`:
`u_ext(x) = (-(α/2) x₀, -(α/2) x₁, α x₂)`. -/
@[expose] public noncomputable def burgersLinearStrain (α : ℝ) (x : T3) : T3 :=
  (-(α / 2) * x 0) • stdBasisVec 0 +
    (-(α / 2) * x 1) • stdBasisVec 1 +
    (α * x 2) • stdBasisVec 2

/-- Coordinate formula for `burgersLinearStrain`. -/
public theorem burgersLinearStrain_coord (α : ℝ) (x : T3) :
    burgersLinearStrain α x 0 = -(α / 2) * x 0 ∧
    burgersLinearStrain α x 1 = -(α / 2) * x 1 ∧
    burgersLinearStrain α x 2 = α * x 2 := by
  unfold burgersLinearStrain stdBasisVec
  refine ⟨?_, ?_, ?_⟩ <;> simp

/-- The global Burgers linear background strain `burgersLinearStrain α` is divergence-free on `ℝ³`
(`div(u_ext) = -(α/2) - (α/2) + α = 0`). -/
public theorem burgersLinearStrain_div_zero (α : ℝ) (x : T3) :
    div (burgersLinearStrain α) x = 0 := by
  unfold div
  rw [Fin.sum_univ_three]
  have h0 : (fun y : T3 => burgersLinearStrain α y 0) = fun y => -(α / 2) * y 0 := by
    funext y; exact (burgersLinearStrain_coord α y).1
  have h1 : (fun y : T3 => burgersLinearStrain α y 1) = fun y => -(α / 2) * y 1 := by
    funext y; exact (burgersLinearStrain_coord α y).2.1
  have h2 : (fun y : T3 => burgersLinearStrain α y 2) = fun y => α * y 2 := by
    funext y; exact (burgersLinearStrain_coord α y).2.2
  rw [h0, h1, h2]
  have hd0 : (fderiv ℝ (fun y : T3 => -(α / 2) * y 0) x) (EuclideanSpace.single 0 1) = -(α / 2) := by
    have hfun : (fun y : T3 => -(α / 2) * y 0) = (-(α / 2)) • (fun y : T3 => y 0) := by
      funext y; simp [Pi.smul_apply, smul_eq_mul]
    rw [hfun, fderiv_const_smul_field, Pi.smul_apply, ContinuousLinearMap.smul_apply,
      fderiv_coord, smul_eq_mul]
    simp
  have hd1 : (fderiv ℝ (fun y : T3 => -(α / 2) * y 1) x) (EuclideanSpace.single 1 1) = -(α / 2) := by
    have hfun : (fun y : T3 => -(α / 2) * y 1) = (-(α / 2)) • (fun y : T3 => y 1) := by
      funext y; simp [Pi.smul_apply, smul_eq_mul]
    rw [hfun, fderiv_const_smul_field, Pi.smul_apply, ContinuousLinearMap.smul_apply,
      fderiv_coord, smul_eq_mul]
    simp
  have hd2 : (fderiv ℝ (fun y : T3 => α * y 2) x) (EuclideanSpace.single 2 1) = α := by
    have hfun : (fun y : T3 => α * y 2) = α • (fun y : T3 => y 2) := by
      funext y; simp [Pi.smul_apply, smul_eq_mul]
    rw [hfun, fderiv_const_smul_field, Pi.smul_apply, ContinuousLinearMap.smul_apply,
      fderiv_coord, smul_eq_mul]
    simp
  rw [hd0, hd1, hd2]
  ring

/-- **Global Burgers Background Strain Violates `IsZ3Periodic` (`burgersLinearStrain_not_z3_periodic`):**
For any non-zero strain rate `α ≠ 0`, `burgersLinearStrain α` is not `ℤ³`-periodic on `ℝ³ / ℤ³`. -/
public theorem burgersLinearStrain_not_z3_periodic (α : ℝ) (hα : α ≠ 0) :
    ¬ IsZ3Periodic (burgersLinearStrain α) := by
  intro hper
  have hshift := z3_periodic_unit_shift hper 0 2
  have hcoord := congrArg (fun v : T3 => v 2) hshift
  simp only [zero_add] at hcoord
  rw [(burgersLinearStrain_coord α (stdBasisVec 2)).2.2,
      (burgersLinearStrain_coord α 0).2.2] at hcoord
  unfold stdBasisVec at hcoord
  simp at hcoord
  exact hα hcoord

/-! ## 3D Cross Product and Biot–Savart Determinant Alignment Depletion -/

/-- Standard 3D Euclidean cross product `a × b` on `T3`. -/
@[expose] public noncomputable def cross3 (a b : T3) : T3 :=
  (a 1 * b 2 - a 2 * b 1) • stdBasisVec 0 +
    (a 2 * b 0 - a 0 * b 2) • stdBasisVec 1 +
    (a 0 * b 1 - a 1 * b 0) • stdBasisVec 2

/-- Standard 3D scalar triple product / determinant `det(a, b, c) = ⟨a, b × c⟩`. -/
@[expose] public noncomputable def det3 (a b c : T3) : ℝ :=
  a 0 * (b 1 * c 2 - b 2 * c 1) +
    a 1 * (b 2 * c 0 - b 0 * c 2) +
    a 2 * (b 0 * c 1 - b 1 * c 0)

/-- The cross product of any vector with itself vanishes: `a × a = 0`. -/
public theorem cross3_self (a : T3) : cross3 a a = 0 := by
  ext i
  unfold cross3 stdBasisVec
  fin_cases i <;> simp <;> ring

/-- When the second and third arguments coincide, `det3 a b b = 0`. -/
public theorem det3_self_right (a b : T3) : det3 a b b = 0 := by
  unfold det3
  ring

/-- **Biot–Savart Determinant Alignment Depletion (`biot_savart_det_aligned_eq_zero`):**
Whenever `ω(x + y) = mag • ξx` is aligned with the vorticity direction `ξx` at `x`, the
determinant factor `det3 yhat (mag • ξx) ξx` in the Biot–Savart stretching kernel vanishes. -/
public theorem biot_savart_det_aligned_eq_zero (yhat ξx : T3) (mag : ℝ) :
    det3 yhat (mag • ξx) ξx = 0 := by
  unfold det3
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

/-- The full Biot–Savart stretching integrand numerator `(yhat · ξx) det(yhat, mag • ξx, ξx)`
vanishes identically when `ω(x + y) = mag • ξx` is parallel to `ξx`. -/
public theorem aligned_vorticity_stretching_integrand_zero (yhat ξx : T3) (mag : ℝ) :
    inner ℝ yhat ξx * det3 yhat (mag • ξx) ξx = 0 := by
  rw [biot_savart_det_aligned_eq_zero, mul_zero]

/-- **Biot–Savart Direction-Difference Identity (`biot_savart_det_difference_identity`):**
For any unit displacement `yhat`, vorticity directions `ξx, ξy`, and magnitude `mag = ‖ω(x+y)‖`,
`det3 yhat (mag • ξy) ξx = mag * det3 yhat (ξy - ξx) ξx`.
Thus non-zero vortex stretching at `x` requires non-zero direction oscillation `ξy - ξx ≠ 0`. -/
public theorem biot_savart_det_difference_identity (yhat ξx ξy : T3) (mag : ℝ) :
    det3 yhat (mag • ξy) ξx = mag * det3 yhat (ξy - ξx) ξx := by
  unfold det3
  simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  ring

/-! ## Navier–Stokes `λ⁶` Scaling Homogeneity vs. Unnormalized `λ⁸` Quartic Mismatch -/

/-- Under Navier–Stokes rescaling `u_λ(x, t) = λ u(λ x, λ² t)`, vorticity scales as `M_λ = λ² M`,
so any cubic vorticity rate `(λ² M)³` scales homogeneously with degree `λ⁶` (`[T⁻³]`). -/
public theorem navier_stokes_vorticity_dt_scaling_exponent (lam : ℝ) :
    (lam ^ 2) ^ 3 = lam ^ 6 := by
  ring

/-- **Scale-Consistent `λ⁶` Homogeneity (`navier_stokes_scaling_homogeneity_deg6`):**
Both the Calderón–Zygmund stretching term `C_CZ M³` and a scale-consistent high-set damping term
`-κ_eff M³` (where `κ_eff M³ = (κ₀ / M) M⁴`) transform with the exact same `λ⁶` homogeneity
under Navier–Stokes rescaling `M ↦ λ² M`. -/
public theorem navier_stokes_scaling_homogeneity_deg6 (lam C_CZ κ_eff M : ℝ) :
    C_CZ * (lam ^ 2 * M) ^ 3 - κ_eff * (lam ^ 2 * M) ^ 3 =
      lam ^ 6 * (C_CZ * M ^ 3 - κ_eff * M ^ 3) := by
  ring

/-- By contrast, an unnormalized quartic term `M⁴` with constant coefficient scales with degree
`λ⁸` (`[T⁻⁴]`) under `M ↦ λ² M`, explaining why a static unnormalized `-κ M⁴` bound cannot hold
uniformly across arbitrary rescalings. -/
public theorem unnormalized_quartic_scaling_mismatch (lam M : ℝ) :
    (lam ^ 2 * M) ^ 4 = lam ^ 8 * M ^ 4 := by
  ring

end FeffermanClayNS
