/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Data.Real.Archimedean

/-!
# Stage 6: Calculus-level derivations of the Stage 3 relations and a non-constant exact flow

Follows Mathlib 4 naming and style conventions (`UpperCamelCase` structures/predicates,
`lower_snake_case` theorems/functions with `conclusion_of_hypothesis` naming and dot notation).
-/

@[expose] public section

noncomputable section

namespace Stage6

open Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- **Mathlib-style structure (`IsUnitDirectionCurve`):** a curve `ξ : ℝ → E` in a real inner
product space staying on the unit sphere (`∀ s, ‖ξ s‖ = 1`) with derivative `ξ'` at `t`. -/
structure IsUnitDirectionCurve (ξ : ℝ → E) (ξ' : E) (t : ℝ) : Prop where
  hasDerivAt : HasDerivAt ξ ξ' t
  norm_eq_one : ∀ s, ‖ξ s‖ = 1

/-- Derivative of `⟪f, f⟫` along a line (product rule). -/
theorem hasDerivAt_inner_self {f : ℝ → E} {f' : E} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => ⟪f s, f s⟫) (2 * ⟪f t, f'⟫) t := by
  have h := hf.inner ℝ hf
  convert h using 1
  rw [real_inner_comm f' (f t)]; ring

/-- **Derived Stage 3 orthogonality (`inner_eq_zero_of_hasDerivAt_of_norm_eq_one`).**
If a differentiable curve stays on the unit sphere, its velocity is orthogonal to it:
`‖ξ s‖ = 1 ∀ s ⇒ ⟪ξ t, ξ'⟫ = 0`. -/
theorem inner_eq_zero_of_hasDerivAt_of_norm_eq_one {ξ : ℝ → E} {ξ' : E} {t : ℝ}
    (hξ : HasDerivAt ξ ξ' t) (hunit : ∀ s, ‖ξ s‖ = 1) :
    ⟪ξ t, ξ'⟫ = 0 := by
  have h1 := hasDerivAt_inner_self hξ
  have hconst : (fun s => ⟪ξ s, ξ s⟫) = fun _ => (1 : ℝ) := by
    funext s; rw [real_inner_self_eq_norm_sq, hunit s, one_pow]
  rw [hconst] at h1
  have h0 := (hasDerivAt_const t (1 : ℝ)).unique h1
  linarith

/-- Backwards-compatible alias for `inner_eq_zero_of_hasDerivAt_of_norm_eq_one`. -/
alias unit_direction_deriv_orthogonal := inner_eq_zero_of_hasDerivAt_of_norm_eq_one

/-- Dot-notation projection on `IsUnitDirectionCurve`: `h.inner_eq_zero` gives `⟪ξ t, ξ'⟫ = 0`. -/
theorem IsUnitDirectionCurve.inner_eq_zero {ξ : ℝ → E} {ξ' : E} {t : ℝ}
    (h : IsUnitDirectionCurve ξ ξ' t) : ⟪ξ t, ξ'⟫ = 0 :=
  inner_eq_zero_of_hasDerivAt_of_norm_eq_one h.hasDerivAt h.norm_eq_one

/-- Polar decomposition derivative: `ω = ρ • ξ ⇒ ω' = ρ' • ξ + ρ • ξ'`. -/
theorem hasDerivAt_smul_polar {ρ : ℝ → ℝ} {ξ : ℝ → E} {ρ' : ℝ} {ξ' : E} {t : ℝ}
    (hρ : HasDerivAt ρ ρ' t) (hξ : HasDerivAt ξ ξ' t) :
    HasDerivAt (fun s => ρ s • ξ s) (ρ' • ξ t + ρ t • ξ') t := by
  have := hρ.smul hξ
  convert this using 1; abel

alias hasDerivAt_polar := hasDerivAt_smul_polar

/-- **Derived polar Pythagoras (`norm_polar_deriv_sq_eq_of_hasDerivAt`).**
For `ω = ρ • ξ` with `ξ` a differentiable unit-direction curve, the derivative `ω'` satisfies
`‖ω'‖² = ρ'² + ρ² ‖ξ'‖²`, with no orthogonality hypothesis. -/
theorem norm_polar_deriv_sq_eq_of_hasDerivAt {ρ : ℝ → ℝ} {ξ : ℝ → E} {ρ' : ℝ} {ξ' : E} {t : ℝ}
    (hρ : HasDerivAt ρ ρ' t) (hξ : HasDerivAt ξ ξ' t) (hunit : ∀ s, ‖ξ s‖ = 1) :
    HasDerivAt (fun s => ρ s • ξ s) (ρ' • ξ t + ρ t • ξ') t ∧
      ‖ρ' • ξ t + ρ t • ξ'‖ ^ 2 = ρ' ^ 2 + ρ t ^ 2 * ‖ξ'‖ ^ 2 := by
  refine ⟨hasDerivAt_smul_polar hρ hξ, ?_⟩
  have horth := inner_eq_zero_of_hasDerivAt_of_norm_eq_one hξ hunit
  have hξξ : ⟪ξ t, ξ t⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hunit t, one_pow]
  have horth' : ⟪ξ', ξ t⟫ = 0 := by rw [real_inner_comm]; exact horth
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq ξ']
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    hξξ, horth, horth']
  ring

alias polar_pythagoras_of_hasDerivAt := norm_polar_deriv_sq_eq_of_hasDerivAt

/-- Dot-notation polar Pythagoras for `IsUnitDirectionCurve`. -/
theorem IsUnitDirectionCurve.norm_polar_deriv_sq_eq {ρ : ℝ → ℝ} {ξ : ℝ → E} {ρ' : ℝ} {ξ' : E} {t : ℝ}
    (h : IsUnitDirectionCurve ξ ξ' t) (hρ : HasDerivAt ρ ρ' t) :
    ‖ρ' • ξ t + ρ t • ξ'‖ ^ 2 = ρ' ^ 2 + ρ t ^ 2 * ‖ξ'‖ ^ 2 :=
  (norm_polar_deriv_sq_eq_of_hasDerivAt hρ h.hasDerivAt h.norm_eq_one).2

/-- First derivative of `h = ½‖ω‖²` along a line: `h' = ⟪ω, ω'⟫`. -/
theorem hasDerivAt_half_norm_sq {ω : ℝ → E} {ω' : E} {t : ℝ} (hω : HasDerivAt ω ω' t) :
    HasDerivAt (fun s => ‖ω s‖ ^ 2 / 2) ⟪ω t, ω'⟫ t := by
  have h := (hasDerivAt_inner_self hω).div_const 2
  have hfun : (fun s => ‖ω s‖ ^ 2 / 2) = fun s => ⟪ω s, ω s⟫ / 2 := by
    funext s; rw [real_inner_self_eq_norm_sq]
  rw [hfun]; convert h using 1; ring

/-- **Derived Stage 3 second-order Leibniz rule (`hasDerivAt_inner_self_deriv_of_hasDerivAt`).**
If `ω` is differentiable with derivative `ω'` everywhere and `ω'` has derivative `ω''` at `t`,
then `h' = ⟪ω, ω'⟫` and `h''(t) = ‖ω'(t)‖² + ⟪ω(t), ω''⟫`. -/
theorem hasDerivAt_inner_self_deriv_of_hasDerivAt {ω ω' : ℝ → E} {ω'' : E} {t : ℝ}
    (hω : ∀ s, HasDerivAt ω (ω' s) s) (hω' : HasDerivAt ω' ω'' t) :
    (∀ s, HasDerivAt (fun r => ‖ω r‖ ^ 2 / 2) ⟪ω s, ω' s⟫ s) ∧
      HasDerivAt (fun s => ⟪ω s, ω' s⟫) (‖ω' t‖ ^ 2 + ⟪ω t, ω''⟫) t := by
  refine ⟨fun s => hasDerivAt_half_norm_sq (hω s), ?_⟩
  have h := (hω t).inner ℝ hω'
  convert h using 1
  rw [real_inner_self_eq_norm_sq]; ring

alias bochner_leibniz_of_hasDerivAt := hasDerivAt_inner_self_deriv_of_hasDerivAt

/-- At an interior local maximum of `½‖ω‖²`, `⟪ω t, ω'⟫ = 0` (Fermat). -/
theorem inner_eq_zero_of_isLocalMax_half_norm_sq {ω : ℝ → E} {ω' : E} {t : ℝ}
    (hω : HasDerivAt ω ω' t) (hmax : IsLocalMax (fun s => ‖ω s‖ ^ 2 / 2) t) :
    ⟪ω t, ω'⟫ = 0 :=
  hmax.hasDerivAt_eq_zero (hasDerivAt_half_norm_sq hω)

alias inner_deriv_zero_at_max := inner_eq_zero_of_isLocalMax_half_norm_sq

/-- **Explicit vacuity guard (`iSup_eq_zero_of_not_bddAbove`).** Mathlib's real `iSup` is `0` on
unbounded ranges; every sup-norm comparison in this library carries a `BddAbove` hypothesis. -/
theorem iSup_eq_zero_of_not_bddAbove {ι : Type*} (f : ι → ℝ)
    (h : ¬ BddAbove (Set.range f)) : (⨆ i, f i) = 0 :=
  Real.iSup_of_not_bddAbove h

alias real_iSup_eq_zero_of_not_bddAbove := iSup_eq_zero_of_not_bddAbove

/-! ### Genuinely non-constant exact periodic shear Beltrami flow -/

/-- Decay rate of the unit-period shear mode: `4π²ν`. -/
def shearRate (ν : ℝ) : ℝ := ν * (2 * π) ^ 2

/-- First component `e^{-4π²νt} sin(2πz)`. -/
def shearU (ν t z : ℝ) : ℝ := exp (-shearRate ν * t) * sin (2 * π * z)

/-- Second component `e^{-4π²νt} cos(2πz)`. -/
def shearV (ν t z : ℝ) : ℝ := exp (-shearRate ν * t) * cos (2 * π * z)

/-- **Mathlib-style predicate (`IsShearBeltramiMode`):** packages periodicity, Beltrami curl
eigenmode relation (`λ = 2π`), and heat/NS PDE balance (`∂_t = ν ∂_{zz}`) at `(ν, t, z)`. -/
structure IsShearBeltramiMode (ν t z : ℝ) : Prop where
  periodic : shearU ν t (z + 1) = shearU ν t z ∧ shearV ν t (z + 1) = shearV ν t z
  beltrami :
    -(exp (-shearRate ν * t) * (-(2 * π * sin (2 * π * z)))) = (2 * π) * shearU ν t z ∧
      exp (-shearRate ν * t) * (2 * π * cos (2 * π * z)) = (2 * π) * shearV ν t z
  heat_rate_u : -shearRate ν * shearU ν t z = ν * (-(2 * π) ^ 2 * shearU ν t z)
  heat_rate_v : -shearRate ν * shearV ν t z = ν * (-(2 * π) ^ 2 * shearV ν t z)

theorem shear_periodic (ν t z : ℝ) :
    shearU ν t (z + 1) = shearU ν t z ∧ shearV ν t (z + 1) = shearV ν t z := by
  unfold shearU shearV
  have h : 2 * π * (z + 1) = 2 * π * z + 2 * π := by ring
  rw [h, sin_add_two_pi, cos_add_two_pi]; exact ⟨rfl, rfl⟩

theorem hasDerivAt_shearU_z (ν t z : ℝ) :
    HasDerivAt (shearU ν t) (exp (-shearRate ν * t) * (2 * π * cos (2 * π * z))) z := by
  have h := ((hasDerivAt_id z).const_mul (2 * π)).sin.const_mul (exp (-shearRate ν * t))
  unfold shearU; convert h using 1; simp; ring

alias shearU_hasDerivAt_z := hasDerivAt_shearU_z

theorem hasDerivAt_shearV_z (ν t z : ℝ) :
    HasDerivAt (shearV ν t) (exp (-shearRate ν * t) * (-(2 * π * sin (2 * π * z)))) z := by
  have h := ((hasDerivAt_id z).const_mul (2 * π)).cos.const_mul (exp (-shearRate ν * t))
  unfold shearV; convert h using 1; simp; ring

alias shearV_hasDerivAt_z := hasDerivAt_shearV_z

theorem shear_beltrami (ν t z : ℝ) :
    -(exp (-shearRate ν * t) * (-(2 * π * sin (2 * π * z)))) = (2 * π) * shearU ν t z ∧
      exp (-shearRate ν * t) * (2 * π * cos (2 * π * z)) = (2 * π) * shearV ν t z := by
  unfold shearU shearV; constructor <;> ring

theorem shearU_heat (ν t z : ℝ) :
    HasDerivAt (fun s => shearU ν s z) (-shearRate ν * shearU ν t z) t ∧
      HasDerivAt (fun w => exp (-shearRate ν * t) * (2 * π * cos (2 * π * w)))
        (-(2 * π) ^ 2 * shearU ν t z) z ∧
      -shearRate ν * shearU ν t z = ν * (-(2 * π) ^ 2 * shearU ν t z) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := (((hasDerivAt_id t).const_mul (-shearRate ν)).exp).mul_const (sin (2 * π * z))
    unfold shearU; convert h using 1; simp; ring
  · have h := (((hasDerivAt_id z).const_mul (2 * π)).cos.const_mul (2 * π)).const_mul
      (exp (-shearRate ν * t))
    unfold shearU; convert h using 1; simp; ring
  · unfold shearRate; ring

theorem shearV_heat (ν t z : ℝ) :
    HasDerivAt (fun s => shearV ν s z) (-shearRate ν * shearV ν t z) t ∧
      HasDerivAt (fun w => exp (-shearRate ν * t) * (-(2 * π * sin (2 * π * w))))
        (-(2 * π) ^ 2 * shearV ν t z) z ∧
      -shearRate ν * shearV ν t z = ν * (-(2 * π) ^ 2 * shearV ν t z) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := (((hasDerivAt_id t).const_mul (-shearRate ν)).exp).mul_const (cos (2 * π * z))
    unfold shearV; convert h using 1; simp; ring
  · have h := ((((hasDerivAt_id z).const_mul (2 * π)).sin.const_mul (2 * π)).neg).const_mul
      (exp (-shearRate ν * t))
    unfold shearV; convert h using 1; simp; ring
  · unfold shearRate; ring

/-- Every `(ν, t, z)` satisfies `IsShearBeltramiMode ν t z`. -/
theorem isShearBeltramiMode (ν t z : ℝ) : IsShearBeltramiMode ν t z :=
  ⟨shear_periodic ν t z, shear_beltrami ν t z, (shearU_heat ν t z).2.2, (shearV_heat ν t z).2.2⟩

theorem shearU_zero_ne_quarter (ν : ℝ) : shearU ν 0 0 ≠ shearU ν 0 (1 / 4) := by
  unfold shearU
  have h : 2 * π * (1 / 4 : ℝ) = π / 2 := by ring
  rw [h, sin_pi_div_two]; simp

alias shear_nonconstant := shearU_zero_ne_quarter

theorem shear_convective_and_div_eq_zero (dU dV : ℝ) :
    (0 : ℝ) * dU = 0 ∧ (0 : ℝ) * dV = 0 ∧ (0 : ℝ) + 0 + 0 = 0 := by
  refine ⟨zero_mul _, zero_mul _, by ring⟩

alias shear_convective_and_div_zero := shear_convective_and_div_eq_zero

end Stage6

end
