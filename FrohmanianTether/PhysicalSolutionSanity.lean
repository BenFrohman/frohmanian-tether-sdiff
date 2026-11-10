/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import FrohmanianTether.NS_Equations
public import Mathlib.Topology.Algebra.Support
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Sanity checks for the repaired `IsPhysicalNSSolution`

The earlier definition (constant extension `u t = u 0` for `t ≤ 0`) forced `∂ₜu(0) = 0` for
every admissible path, so every `KatoLocalWitness` started from steady data. The repaired
definition uses the affine extension `u t = u 0 + t • v₀` for `t ≤ 0`. This file proves:

* `physical_time_deriv_at_zero`: for an admissible path the time derivative at `0` is the slope
  `v₀` of the extension, i.e. the genuine right derivative of the solution;
* `exists_physical_time_deriv_ne_zero`: an explicit admissible path with `∂ₜu(0) ≠ 0`;
* `not_forall_physical_time_deriv_zero`: the old consequence `∂ₜu(0) = 0` no longer follows.

Scope (honest): the explicit path `sanityPath` is a member of the admissibility class
`IsPhysicalNSSolution`; it is NOT claimed to solve the Navier–Stokes equations. No explicit
non-steady Navier–Stokes solution is constructed in this repository.
-/

namespace PhysicalSolutionSanity

open NavierStokes3D MeasureTheory

noncomputable section

/-- For an admissible path, the two-sided time derivative at `t = 0` equals the slope of the
negative-time extension (which is therefore the right derivative of the solution at `0`). -/
public theorem physical_time_deriv_at_zero (u : TimeDependentVelocity)
    (hu : IsPhysicalNSSolution u) (v₀ : VelocityField) (hv₀ : ∀ t ≤ (0 : ℝ), u t = u 0 + t • v₀)
    (x : T3) : deriv (fun s => u s x) 0 = v₀ x := by
  have hd := (hu.1 0 le_rfl x).hasDerivAt
  have hL : HasDerivWithinAt (fun s => u s x) (v₀ x) (Set.Iic 0) 0 := by
    have hlin : HasDerivWithinAt (fun s : ℝ => u 0 x + s • v₀ x) (v₀ x) (Set.Iic 0) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (v₀ x)).const_add (u 0 x)
        |>.hasDerivWithinAt
    refine hlin.congr (fun s hs => ?_) (by simp)
    rw [hv₀ s hs]; rfl
  exact (uniqueDiffOn_Iic (0:ℝ) 0 Set.self_mem_Iic).eq_deriv _ hd.hasDerivWithinAt hL

/-- Time profile: `1 - t` for `t ≤ 0`, `(1 + t)⁻¹` for `t > 0` (C¹ at `0`, slope `-1`). -/
public def g (t : ℝ) : ℝ := if t ≤ 0 then 1 - t else (1 + t)⁻¹

/-- Spatial profile: the continuous compactly supported tent `max 0 (1 - ‖x‖)` times `e₀`. -/
public def φ (x : T3) : EuclideanSpace ℝ (Fin 3) :=
  max 0 (1 - ‖x‖) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)

/-- The explicit admissible, non-steady path `u t x = g t • φ x`. -/
public def sanityPath : TimeDependentVelocity := fun t x => g t • φ x

theorem g_zero : g 0 = 1 := by simp [g]

theorem g_of_pos {t : ℝ} (ht : 0 < t) : g t = (1 + t)⁻¹ := by simp [g, not_le.mpr ht]

theorem g_eq_on_Ici {t : ℝ} (ht : 0 ≤ t) : g t = (1 + t)⁻¹ := by
  rcases ht.lt_or_eq with h | h
  · exact g_of_pos h
  · subst h; simp [g]

theorem g_sq_le_one {t : ℝ} (ht : 0 ≤ t) : g t ^ 2 ≤ 1 := by
  rw [g_eq_on_Ici ht]
  have h1 : 1 ≤ 1 + t := by linarith
  have h0 : 0 < (1 + t)⁻¹ := inv_pos.mpr (by linarith)
  have hle : (1 + t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
  nlinarith

theorem hasDerivAt_g_zero : HasDerivAt g (-1) 0 := by
  have hL : HasDerivWithinAt g (-1) (Set.Iic 0) 0 := by
    have : HasDerivAt (fun t : ℝ => 1 - t) (-1) 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).const_sub 1
    refine this.hasDerivWithinAt.congr (fun s hs => ?_) (by simp [g])
    simp [g, Set.mem_Iic.mp hs]
  have hR : HasDerivWithinAt g (-1) (Set.Ici 0) 0 := by
    have : HasDerivAt (fun t : ℝ => (1 + t)⁻¹) (-1) 0 := by
      have h := ((hasDerivAt_id (0:ℝ)).const_add 1).inv (by norm_num)
      simpa using h
    refine this.hasDerivWithinAt.congr (fun s hs => ?_) (by simp [g])
    exact g_eq_on_Ici hs
  have := hL.union hR
  rwa [Set.Iic_union_Ici, hasDerivWithinAt_univ] at this

theorem differentiableAt_g {t : ℝ} (ht : 0 ≤ t) : DifferentiableAt ℝ g t := by
  rcases ht.lt_or_eq with h | h
  · have hev : (fun s : ℝ => (1 + s)⁻¹) =ᶠ[nhds t] g := by
      filter_upwards [lt_mem_nhds h] with s hs
      exact (g_of_pos hs).symm
    have hd : DifferentiableAt ℝ (fun s : ℝ => (1 + s)⁻¹) t :=
      ((differentiableAt_id).const_add 1).inv (by simp; linarith)
    exact hd.congr_of_eventuallyEq hev.symm
  · subst h; exact hasDerivAt_g_zero.differentiableAt

theorem continuous_φ : Continuous φ := by
  unfold φ
  fun_prop

theorem hasCompactSupport_normSq_φ : HasCompactSupport (fun x : T3 => ‖φ x‖ ^ 2) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : T3) 1) (fun x hx => ?_)
  have hx' : 1 < ‖x‖ := by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hx
  have : max 0 (1 - ‖x‖) = 0 := max_eq_left (by linarith)
  simp [φ, this]

theorem integrable_normSq_φ : Integrable (fun x : T3 => ‖φ x‖ ^ 2) :=
  ((continuous_φ.norm).pow 2).integrable_of_hasCompactSupport hasCompactSupport_normSq_φ

theorem normSq_sanityPath (t : ℝ) (x : T3) :
    ‖sanityPath t x‖ ^ 2 = g t ^ 2 * ‖φ x‖ ^ 2 := by
  simp [sanityPath, norm_smul, mul_pow, sq_abs]

/-- `sanityPath` is in the repaired admissibility class. -/
public theorem sanityPath_isPhysical : IsPhysicalNSSolution sanityPath := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht x
    exact (differentiableAt_g ht).smul_const (φ x)
  · intro t _ht
    exact continuous_const.smul continuous_φ
  · intro t _ht
    simp only [normSq_sanityPath]
    exact integrable_normSq_φ.const_mul _
  · intro t ht
    simp only [normSq_sanityPath, g_zero, one_pow, one_mul]
    rw [integral_const_mul]
    have hnn : 0 ≤ ∫ x, ‖φ x‖ ^ 2 ∂volume := integral_nonneg (fun _ => sq_nonneg _)
    calc g t ^ 2 * ∫ x, ‖φ x‖ ^ 2 ∂volume ≤ 1 * ∫ x, ‖φ x‖ ^ 2 ∂volume :=
          mul_le_mul_of_nonneg_right (g_sq_le_one ht) hnn
      _ = _ := one_mul _
  · refine ⟨fun x => -φ x, fun t ht => ?_⟩
    funext x
    have h0 : g 0 = 1 := g_zero
    simp only [sanityPath, Pi.add_apply, Pi.smul_apply, h0, one_smul]
    simp only [g, if_pos ht]
    rw [sub_smul, one_smul, smul_neg, sub_eq_add_neg]

/-- **Sanity lemma.** The repaired class contains a path whose time derivative at `t = 0`
is nonzero (at `x = 0` it is `-e₀`). -/
public theorem exists_physical_time_deriv_ne_zero :
    ∃ u : TimeDependentVelocity, IsPhysicalNSSolution u ∧
      ∃ x : T3, deriv (fun s => u s x) 0 ≠ 0 := by
  refine ⟨sanityPath, sanityPath_isPhysical, 0, ?_⟩
  have h : HasDerivAt (fun s => sanityPath s 0) ((-1 : ℝ) • φ 0) 0 :=
    hasDerivAt_g_zero.smul_const (φ 0)
  rw [h.deriv]
  intro h0
  have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) h0
  simp [φ] at h1

/-- **Sanity lemma.** The old consequence of the constant extension, `∂ₜu(0) = 0` for every
admissible path, is false for the repaired class. -/
public theorem not_forall_physical_time_deriv_zero :
    ¬ ∀ u : TimeDependentVelocity, IsPhysicalNSSolution u →
      ∀ x : T3, deriv (fun s => u s x) 0 = 0 := by
  intro h
  obtain ⟨u, hu, x, hx⟩ := exists_physical_time_deriv_ne_zero
  exact hx (h u hu x)

end

end PhysicalSolutionSanity

#print axioms PhysicalSolutionSanity.physical_time_deriv_at_zero
#print axioms PhysicalSolutionSanity.sanityPath_isPhysical
#print axioms PhysicalSolutionSanity.exists_physical_time_deriv_ne_zero
#print axioms PhysicalSolutionSanity.not_forall_physical_time_deriv_zero
