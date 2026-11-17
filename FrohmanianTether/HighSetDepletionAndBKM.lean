/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import FrohmanianTether.TorusStrainExclusion

/-!
# FrohmanianTether.HighSetDepletionAndBKM

Machine-checked Lean 4 module.
-/

open scoped BigOperators Gradient Topology
open ENNReal InnerProductSpace MeasureTheory Finset Filter
open NavierStokes3D

/-!
# Conditional Reduction of Fefferman's Periodic Problem (B) via High-Set Direction Depletion & BKM

This module formalizes the **conditional** analytic reduction chain on `𝕋³ = ℝ³ / ℤ³`:

1. **Pointwise Maximum-Vorticity Rate Reduction (`unmodified_max_rate_of_cubic_source`,
   `viscous_direction_dissipation_bridge`, `scale_invariant_cubic_rate_of_direction_coercivity`):**
   At a spatial maximum `x_t` where `M = ‖ω(t, x_t)‖ > 0` and `(u · ∇)‖ω‖²(x_t) = 0`, dividing the
   unmodified vorticity norm-squared identity by `2 M` reduces the time-derivative bound for `M(t)`
   to the sum of vortex stretching `⟨ω, (ω · ∇) u⟩` and viscous dissipation `ν ⟨ω, Δω⟩`.
   When viscous direction-gradient dissipation `-ν M² ‖∇ξ‖²` satisfies a high-vorticity coercivity
   estimate on `𝕋³`, it yields a cubic comparison differential inequality.

2. **Cubic Comparison ODE Ceiling (`comparison_ode_ceiling`):**
   Unconditional proof (via `image_le_of_deriv_right_lt_deriv_boundary`) that any differentiable
   trajectory `M : ℝ → ℝ` on `[0, T]` satisfying `deriv M t ≤ C_CZ * M(t)² - κ'' * M(t)³` with
   `C_CZ > 0` and `κ'' > 0` is uniformly bounded by `Y = max (M 0) (C_CZ / κ'')`.

3. **Explicit Conditional Reductions to `Clay_B_exact` (`clay_B_exact_of_periodic_tether_bound`,
   `clay_B_exact_of_torus_direction_depletion`):**
   These theorems are **CONDITIONAL reductions**. Their hypotheses (`PeriodicDirectionDepletionBound ν`,
   `PeriodicTetherClosingBound ν`, and `PeriodicBKMContinuation ν`) are stated explicitly as
   hypotheses in the theorem signatures, never as axioms. Establishing `PeriodicDirectionDepletionBound ν`
   (or `PeriodicTetherClosingBound ν`) for arbitrary smooth `ℤ³`-periodic initial data remains OPEN.
-/

namespace FrohmanianTether.HighSetDepletionAndBKM
open FrohmanianTether.ClayStatements
open FrohmanianTether.TorusStrainExclusion

/-- **Pointwise Unmodified Maximum-Vorticity Rate Reduction (`unmodified_max_rate_of_cubic_source`):**
If `M > 0`, `M' ≤ (⟨ω, (ω · ∇) u⟩ - (u · ∇)‖ω‖² / 2 + ν ⟨ω, Δω⟩) / M`, the convective transport
of `‖ω‖²` vanishes at the spatial maximum (`hconv_max : conv_norm_sq = 0`), and the net source
satisfies `stretching + ν * visc_lap ≤ C_CZ * M ^ 3 - κ'' * M ^ 4`, then
`M' ≤ C_CZ * M ^ 2 - κ'' * M ^ 3`. -/
public theorem unmodified_max_rate_of_cubic_source
    (M M' stretching conv_norm_sq ν visc_lap C_CZ κ'' : ℝ)
    (hM_pos : 0 < M)
    (h_unmod_id : M' ≤ (stretching - conv_norm_sq / 2 + ν * visc_lap) / M)
    (hconv_max : conv_norm_sq = 0)
    (h_source : stretching + ν * visc_lap ≤ C_CZ * M ^ 3 - κ'' * M ^ 4) :
    M' ≤ C_CZ * M ^ 2 - κ'' * M ^ 3 := by
  have h1 : stretching - conv_norm_sq / 2 + ν * visc_lap ≤ C_CZ * M ^ 3 - κ'' * M ^ 4 := by
    rw [hconv_max]
    linarith
  have h2 : (stretching - conv_norm_sq / 2 + ν * visc_lap) / M ≤
      (C_CZ * M ^ 3 - κ'' * M ^ 4) / M :=
    div_le_div_of_nonneg_right h1 (le_of_lt hM_pos)
  have hM_ne : M ≠ 0 := ne_of_gt hM_pos
  have h3 : (C_CZ * M ^ 3 - κ'' * M ^ 4) / M = C_CZ * M ^ 2 - κ'' * M ^ 3 := by
    field_simp [hM_ne]
  linarith

/-- **Viscous Direction-Gradient Dissipation Bridge (`viscous_direction_dissipation_bridge`):**
At a spatial maximum `M > 0` where `conv_norm_sq = 0`, if vortex stretching satisfies
`stretching ≤ C_CZ * M ^ 3`, viscous dissipation satisfies the direction-gradient decomposition
`ν * visc_lap ≤ -ν * M ^ 2 * grad_xi_sq`, and the high-vorticity direction gradient satisfies
`ν * grad_xi_sq ≥ κ'' * M ^ 2`, then `M' ≤ C_CZ * M ^ 2 - κ'' * M ^ 3`. -/
public theorem viscous_direction_dissipation_bridge
    (M M' stretching conv_norm_sq ν visc_lap grad_xi_sq C_CZ κ'' : ℝ)
    (hM_pos : 0 < M)
    (h_unmod_id : M' ≤ (stretching - conv_norm_sq / 2 + ν * visc_lap) / M)
    (hconv_max : conv_norm_sq = 0)
    (h_stretch : stretching ≤ C_CZ * M ^ 3)
    (h_visc_decomp : ν * visc_lap ≤ -(ν * M ^ 2 * grad_xi_sq))
    (h_dir_coercive : κ'' * M ^ 2 ≤ ν * grad_xi_sq) :
    M' ≤ C_CZ * M ^ 2 - κ'' * M ^ 3 := by
  have hM2_nonneg : 0 ≤ M ^ 2 := sq_nonneg M
  have h_dissip : κ'' * M ^ 4 ≤ ν * M ^ 2 * grad_xi_sq := by
    calc
      κ'' * M ^ 4 = M ^ 2 * (κ'' * M ^ 2) := by ring
      _ ≤ M ^ 2 * (ν * grad_xi_sq) := mul_le_mul_of_nonneg_left h_dir_coercive hM2_nonneg
      _ = ν * M ^ 2 * grad_xi_sq := by ring
  have h_source : stretching + ν * visc_lap ≤ C_CZ * M ^ 3 - κ'' * M ^ 4 := by
    linarith
  exact unmodified_max_rate_of_cubic_source M M' stretching conv_norm_sq ν visc_lap C_CZ κ''
    hM_pos h_unmod_id hconv_max h_source

/-- **Scale-Invariant Cubic Rate under `λ⁶` Direction Coercivity (`scale_invariant_cubic_rate_of_direction_coercivity`):**
When the viscous direction-gradient dissipation satisfies the scale-invariant `λ⁶`-homogeneous
bound `ν * grad_xi_sq ≥ κ_eff * M` (so `ν * M ^ 2 * grad_xi_sq ≥ κ_eff * M ^ 3`), both the
stretching bound `C_CZ * M ^ 3` and the viscous direction dissipation `-κ_eff * M ^ 3` have
cubic degree in `M` (`λ⁶` under Navier–Stokes rescaling), yielding `M' ≤ (C_CZ - κ_eff) * M ^ 2`. -/
public theorem scale_invariant_cubic_rate_of_direction_coercivity
    (M M' stretching conv_norm_sq ν visc_lap grad_xi_sq C_CZ κ_eff : ℝ)
    (hM_pos : 0 < M)
    (h_unmod_id : M' ≤ (stretching - conv_norm_sq / 2 + ν * visc_lap) / M)
    (hconv_max : conv_norm_sq = 0)
    (h_stretch : stretching ≤ C_CZ * M ^ 3)
    (h_visc_decomp : ν * visc_lap ≤ -(ν * M ^ 2 * grad_xi_sq))
    (h_scale_coercive : κ_eff * M ≤ ν * grad_xi_sq) :
    M' ≤ (C_CZ - κ_eff) * M ^ 2 := by
  have hM2_nonneg : 0 ≤ M ^ 2 := sq_nonneg M
  have h_dissip : κ_eff * M ^ 3 ≤ ν * M ^ 2 * grad_xi_sq := by
    calc
      κ_eff * M ^ 3 = M ^ 2 * (κ_eff * M) := by ring
      _ ≤ M ^ 2 * (ν * grad_xi_sq) := mul_le_mul_of_nonneg_left h_scale_coercive hM2_nonneg
      _ = ν * M ^ 2 * grad_xi_sq := by ring
  have h1 : stretching - conv_norm_sq / 2 + ν * visc_lap ≤ (C_CZ - κ_eff) * M ^ 3 := by
    rw [hconv_max]
    linarith
  have h2 : (stretching - conv_norm_sq / 2 + ν * visc_lap) / M ≤
      ((C_CZ - κ_eff) * M ^ 3) / M :=
    div_le_div_of_nonneg_right h1 (le_of_lt hM_pos)
  have hM_ne : M ≠ 0 := ne_of_gt hM_pos
  have h3 : ((C_CZ - κ_eff) * M ^ 3) / M = (C_CZ - κ_eff) * M ^ 2 := by
    field_simp [hM_ne]
  linarith

/-- Factorization of the cubic comparison vector field `C_CZ * z² - κ'' * z³ = z² * (C_CZ - κ'' * z)`. -/
public theorem cubic_comparison_field_eq (C_CZ κ'' z : ℝ) :
    C_CZ * z ^ 2 - κ'' * z ^ 3 = z ^ 2 * (C_CZ - κ'' * z) := by
  ring

/-- Strictly above the threshold `C_CZ / κ''`, the cubic comparison vector field is negative. -/
public theorem cubic_comparison_field_neg_of_gt
    {C_CZ κ'' z : ℝ} (hC : 0 < C_CZ) (hκ : 0 < κ'') (hz : C_CZ / κ'' < z) :
    C_CZ * z ^ 2 - κ'' * z ^ 3 < 0 := by
  have hzpos : 0 < z := lt_trans (div_pos hC hκ) hz
  have hz2 : 0 < z ^ 2 := sq_pos_of_pos hzpos
  have hlin : C_CZ - κ'' * z < 0 := by
    have hmul : κ'' * (C_CZ / κ'') < κ'' * z := mul_lt_mul_of_pos_left hz hκ
    rw [mul_div_cancel₀ C_CZ (ne_of_gt hκ)] at hmul
    linarith [hmul]
  rw [cubic_comparison_field_eq]
  exact mul_neg_of_pos_of_neg hz2 hlin

/-- **Cubic Comparison ODE Stability Ceiling (`comparison_ode_ceiling`):**
For any differentiable trajectory `M : ℝ → ℝ` on `[0, T]` satisfying the cubic differential
inequality `deriv M t ≤ C_CZ * (M t)² - κ'' * (M t)³` with `C_CZ > 0` and `κ'' > 0`,
`M t ≤ max (M 0) (C_CZ / κ'')` for every `t ∈ [0, T]`. -/
public theorem comparison_ode_ceiling
    (M : ℝ → ℝ) (T C_CZ κ'' : ℝ)
    (hC_pos : 0 < C_CZ) (hκ_pos : 0 < κ'')
    (hM_diff : ∀ t ∈ Set.Icc (0 : ℝ) T, DifferentiableAt ℝ M t)
    (hODE : ∀ t ∈ Set.Icc (0 : ℝ) T, deriv M t ≤ C_CZ * (M t) ^ 2 - κ'' * (M t) ^ 3) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, M t ≤ max (M 0) (C_CZ / κ'') := by
  intro t ht
  set Y := max (M 0) (C_CZ / κ'')
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hbarrier : C_CZ / κ'' < Y + ε :=
    lt_of_le_of_lt (le_max_right (M 0) (C_CZ / κ'')) (lt_add_of_pos_right _ hε)
  have hM0 : M 0 ≤ Y + ε :=
    (le_max_left (M 0) (C_CZ / κ'')).trans (le_add_of_nonneg_right hε.le)
  have hMC : ContinuousOn M (Set.Icc (0 : ℝ) t) := fun x hx =>
    (hM_diff x ⟨hx.1, le_trans hx.2 ht.2⟩).continuousAt.continuousWithinAt
  have hMW : ∀ x ∈ Set.Ico (0 : ℝ) t,
      HasDerivWithinAt M (deriv M x) (Set.Ici x) x := fun x hx =>
    (hM_diff x ⟨hx.1, le_trans (le_of_lt hx.2) ht.2⟩).hasDerivAt.hasDerivWithinAt
  have hB : ∀ x, HasDerivAt (fun _ : ℝ => Y + ε) (0 : ℝ) x := fun x =>
    hasDerivAt_const x (Y + ε)
  have hcontact : ∀ x ∈ Set.Ico (0 : ℝ) t, M x = Y + ε → deriv M x < 0 := by
    intro x hx hxeq
    have hneg : C_CZ * (Y + ε) ^ 2 - κ'' * (Y + ε) ^ 3 < 0 :=
      cubic_comparison_field_neg_of_gt hC_pos hκ_pos hbarrier
    have hdot := hODE x ⟨hx.1, le_trans (le_of_lt hx.2) ht.2⟩
    rw [hxeq] at hdot
    linarith
  have hle :=
    image_le_of_deriv_right_lt_deriv_boundary (f := M) (f' := deriv M)
      (a := 0) (b := t) (B := fun _ => Y + ε) (B' := fun _ => (0 : ℝ))
      hMC hMW hM0 hB hcontact
  exact hle ⟨ht.1, le_rfl⟩

/-! ## Conditional Periodic Hypotheses & Conditional Reductions to `Clay_B_exact`

**Honesty & Scope Notice:**
Both `PeriodicDirectionDepletionBound ν` and `PeriodicTetherClosingBound ν` are **OPEN**
analytic hypotheses on the periodic 3-torus `𝕋³ = ℝ³ / ℤ³`. They are defined as `Prop`s and
passed explicitly as hypotheses to the conditional reduction theorems
`clay_B_exact_of_periodic_tether_bound` and `clay_B_exact_of_torus_direction_depletion`. -/

/-- **Conditional Hypothesis 1a (`PeriodicDirectionDepletionBound` — OPEN):**
For every smooth, divergence-free, `ℤ³`-periodic initial datum `u₀`, there exist positive
constants `C_CZ, κ'' > 0` such that along any local-in-time periodic smooth solution `(u, p)` on
`[0, T) × (ℝ³ / ℤ³)`, the spatial supremum of vorticity `M(t) = ‖ω(t)‖_∞` obeys the uniform
ceiling `M(t) ≤ max ‖ω₀‖_∞ (C_CZ / κ'')` induced by the cubic direction-depletion differential
inequality `M' ≤ C_CZ M² - κ'' M³` (`comparison_ode_ceiling`). -/
@[expose] public def PeriodicDirectionDepletionBound (ν : ℝ) : Prop :=
  ∀ u₀ : VelocityField,
    (∀ x, div u₀ x = 0) → ContDiff ℝ (⊤ : ℕ∞) u₀ → IsZ3Periodic u₀ →
      ∃ C κ_dir : ℝ, 0 < C ∧ 0 < κ_dir ∧
        ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
          IsPeriodicSmoothSolutionOn ν T u₀ u p →
            ∀ t ∈ Set.Ico (0 : ℝ) T,
              vorticity_sup_norm (vorticity (u t)) ≤
                max (vorticity_sup_norm (vorticity u₀)) (C / κ_dir)

/-- **Proved (standard axioms): Periodic Direction Depletion Bound implies Periodic Tether Closing Bound.** -/
public theorem periodicTetherClosingBound_of_directionDepletion
    {ν : ℝ} (hdepl : PeriodicDirectionDepletionBound ν) :
    PeriodicTetherClosingBound ν := by
  intro u₀ hdiv hsm hper
  obtain ⟨C, κ_dir, _hC, _hκ, hbound⟩ := hdepl u₀ hdiv hsm hper
  refine ⟨max (vorticity_sup_norm (vorticity u₀)) (C / κ_dir), ?_⟩
  intro T u p hsol t ht
  exact hbound T u p hsol t ht

/-- **CONDITIONAL Reduction (`clay_B_exact_of_torus_direction_depletion`):**
If for every `ν > 0`, smooth periodic Navier–Stokes flows on `ℝ³/ℤ³` satisfy the direction
depletion bound (`PeriodicDirectionDepletionBound ν`, OPEN) and classical periodic BKM
continuation (`PeriodicBKMContinuation ν`, OPEN), then `Clay_B_exact` holds. -/
public theorem clay_B_exact_of_torus_direction_depletion
    (hdepl : ∀ ν > (0 : ℝ), PeriodicDirectionDepletionBound ν)
    (hBKM : ∀ ν > (0 : ℝ), PeriodicBKMContinuation ν) :
    Clay_B_exact :=
  clay_B_exact_of_periodic_tether_bound
    (fun ν hν => periodicTetherClosingBound_of_directionDepletion (hdepl ν hν))
    hBKM

#print axioms unmodified_max_rate_of_cubic_source
#print axioms viscous_direction_dissipation_bridge
#print axioms scale_invariant_cubic_rate_of_direction_coercivity
#print axioms comparison_ode_ceiling
#print axioms periodicTetherClosingBound_of_directionDepletion
#print axioms clay_B_exact_of_torus_direction_depletion

end FrohmanianTether.HighSetDepletionAndBKM
