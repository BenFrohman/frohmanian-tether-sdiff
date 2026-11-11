/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import FrohmanianTether.ExplicitFlows

/-!
# Definition audit (0.1.5): the two defects of the 0.1.4 tether hypotheses

This file records, in Lean, the two definitional defects found in the 0.1.4 encodings of the
local tether hypotheses, and keeps the 0.1.4 definitions verbatim under the suffix `V014` so
that the defects are checkable against the exact published text.

1. **Junk value of the supremum (flag 1).** `vorticity_sup_norm ω = ⨆ x, ‖ω x‖` is a real
   `iSup`, which Mathlib sets to `0` when the range is not bounded above
   (`vorticity_sup_norm_eq_zero_of_not_bddAbove`). The 0.1.4 `LocalTetherBound` had no
   `BddAbove` clause, so it imposed **no constraint at any time at which `ω(t)` is unbounded**
   (`localTetherBoundV014_constraint_free_of_unbounded`). The 0.1.5 definitions add the clause.

2. **Two-sided differentiability at the right endpoint (flag 2).** The 0.1.4 `LocalTetherRate`
   demanded `DifferentiableAt ℝ M s` for `M(t) = ‖ω(t)‖_∞` at every `s ∈ [0, T]`. At `s = T`
   this depends on the path for `t > T`, where a local solution on `[0, T]` is unconstrained.
   `escapePath` is a local physical solution on `[0, 0]` from `u₀ = 0`
   (`isLocalPhysicalSolution_escapePath`) whose `M(t) = t⁻¹` for `t > 0`
   (`vorticity_sup_norm_escapePath_pos`), so `M` is not even continuous at `0`. Hence
   `LocalTetherRateV014 0 ν` is **false** (`not_localTetherRateV014_zero`), and the hypothesis
   `hDI : ∀ u₀ ν, LocalTetherRateV014 u₀ ν` of the 0.1.4 `frohmanian_tether_theorem` was
   unsatisfiable (`not_forall_localTetherRateV014`): that theorem was vacuously true. The 0.1.5
   `LocalTetherRate` uses a right derivative (`HasDerivWithinAt … (Set.Ici s) s`) only for
   `s ∈ [0, T)` plus `ContinuousOn` on `[0, T]`, so it only reads the path on `[0, T]`.
-/

open MeasureTheory NavierStokes3D Filter Topology
open scoped ContDiff

noncomputable section

namespace FrohmanianTether.TetherDefinitionAudit

open ExplicitFlows

/-! ## Flag 1: the junk value of `vorticity_sup_norm` -/

/-- `vorticity_sup_norm` of a field with unbounded norm is the junk value `0`. -/
public theorem vorticity_sup_norm_eq_zero_of_not_bddAbove {w : VorticityField}
    (h : ¬ BddAbove (Set.range fun x => ‖w x‖)) : vorticity_sup_norm w = 0 :=
  Real.iSup_of_not_bddAbove h

/-- **0.1.4 `LocalTetherBound`, verbatim** (superseded in 0.1.5 by the `BddAbove`-guarded form). -/
@[expose] public def LocalTetherBoundV014 (u₀ : VelocityField) (ν : ℝ) : Prop :=
  ∃ Y : ℝ, ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
    IsLocalPhysicalSolution ν T u₀ u p →
      ∀ t ∈ Set.Icc (0 : ℝ) T, vorticity_sup_norm (vorticity (u t)) ≤ Y

/-- At any time where the vorticity is unbounded, the 0.1.4 ceiling holds with every `Y ≥ 0`:
the 0.1.4 `LocalTetherBound` imposed no constraint there. -/
public theorem localTetherBoundV014_constraint_free_of_unbounded {u : TimeDependentVelocity}
    {t Y : ℝ} (hY : 0 ≤ Y) (h : ¬ BddAbove (Set.range fun x => ‖vorticity (u t) x‖)) :
    vorticity_sup_norm (vorticity (u t)) ≤ Y := by
  rw [vorticity_sup_norm_eq_zero_of_not_bddAbove h]
  exact hY

/-- **Every** smooth divergence-free finite-energy datum has a local physical solution on the
degenerate interval `[0, 0]`: the affine path `u₀ + t • v₀` with `v₀ = ν Δu₀ − (u₀·∇)u₀` and
zero pressure. So the time-`0` clause of a local-solution hypothesis is never vacuous. -/
public theorem exists_isLocalPhysicalSolution_zero_time (ν : ℝ) {u₀ : VelocityField}
    (hsm : ContDiff ℝ (⊤ : ℕ∞) u₀) (hdiv : ∀ x, div u₀ x = 0)
    (hE : Integrable (fun x : T3 => ‖u₀ x‖ ^ 2)) :
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure), IsLocalPhysicalSolution ν 0 u₀ u p := by
  set v₀ : VelocityField := fun x => ν • laplacian u₀ x - convective u₀ u₀ x
  set u : TimeDependentVelocity := fun t => u₀ + t • v₀
  have hu0 : u 0 = u₀ := by simp [u]
  have hder : ∀ (t : ℝ) (x : T3), HasDerivAt (fun s => u s x) (v₀ x) t := by
    intro t x
    have h := ((hasDerivAt_id t).smul_const (v₀ x)).const_add (u₀ x)
    simpa [u] using h
  refine ⟨u, fun _ => 0, hu0, ?_, ?_, ?_⟩
  · intro t ht x
    obtain rfl : t = 0 := le_antisymm ht.2 ht.1
    rw [hu0]
    refine ⟨?_, hdiv x⟩
    have hdt : time_deriv u 0 x = v₀ x := (hder 0 x).deriv
    have hp : pressureGradient ((fun _ => (0 : PressureField)) 0) x = 0 :=
      pressureGradient_const 0 x
    rw [hdt, hp]
    simp [v₀]
  · intro t ht
    obtain rfl : t = 0 := le_antisymm ht.2 ht.1
    rw [hu0]; exact hsm
  · refine ⟨fun t _ x => (hder t x).differentiableAt, ?_, ?_, ?_, ⟨v₀, fun t _ => by simp [u]⟩⟩
    · intro t ht
      obtain rfl : t = 0 := le_antisymm ht.2 ht.1
      rw [hu0]; exact hsm.continuous
    · intro t ht
      obtain rfl : t = 0 := le_antisymm ht.2 ht.1
      rw [hu0]; exact hE
    · intro t ht
      obtain rfl : t = 0 := le_antisymm ht.2 ht.1
      exact le_rfl

/-- With the 0.1.5 `BddAbove` clause, a datum with **unbounded** initial vorticity never satisfies
`LocalTetherBound` (its degenerate solution on `[0, 0]` violates the clause). This is why the
0.1.5 closing bound and `frohmanian_tether_theorem` restrict to data with bounded `ω₀`. -/
public theorem not_localTetherBound_of_unbounded (ν : ℝ) {u₀ : VelocityField}
    (hsm : ContDiff ℝ (⊤ : ℕ∞) u₀) (hdiv : ∀ x, div u₀ x = 0)
    (hE : Integrable (fun x : T3 => ‖u₀ x‖ ^ 2))
    (hω : ¬ BddAbove (Set.range fun x => ‖vorticity u₀ x‖)) :
    ¬ TetheredLyapunov.LocalTetherBound u₀ ν := by
  rintro ⟨Y, hY⟩
  obtain ⟨u, p, hu⟩ := exists_isLocalPhysicalSolution_zero_time ν hsm hdiv hE
  have h := (hY 0 u p hu 0 ⟨le_rfl, le_rfl⟩).1
  rw [hu.1] at h
  exact hω h

/-- Likewise for the 0.1.5 `LocalTetherRate`. -/
public theorem not_localTetherRate_of_unbounded (ν : ℝ) {u₀ : VelocityField}
    (hsm : ContDiff ℝ (⊤ : ℕ∞) u₀) (hdiv : ∀ x, div u₀ x = 0)
    (hE : Integrable (fun x : T3 => ‖u₀ x‖ ^ 2))
    (hω : ¬ BddAbove (Set.range fun x => ‖vorticity u₀ x‖)) :
    ¬ TetheredLyapunov.LocalTetherRate u₀ ν := fun h =>
  not_localTetherBound_of_unbounded ν hsm hdiv hE hω
    (TetheredLyapunov.localTetherBound_of_localTetherRate h)

/-! ## Flag 2: two-sided differentiability at the endpoint -/

/-- **0.1.4 `LocalTetherRate`, verbatim** (superseded in 0.1.5). -/
@[expose] public def LocalTetherRateV014 (u₀ : VelocityField) (ν : ℝ) : Prop :=
  ∃ C κ'' : ℝ, 0 < C ∧ 0 < κ'' ∧
    ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsLocalPhysicalSolution ν T u₀ u p →
        (∀ s ∈ Set.Icc (0 : ℝ) T,
          DifferentiableAt ℝ (fun τ => vorticity_sup_norm (vorticity (u τ))) s) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) T,
          deriv (fun τ => vorticity_sup_norm (vorticity (u τ))) s ≤
            C * vorticity_sup_norm (vorticity (u s)) ^ 2 -
              κ'' * vorticity_sup_norm (vorticity (u s)) ^ 3)

/-- The unit Beltrami profile `(sin(k x₂), cos(k x₂), 0)` has unit length everywhere. -/
public theorem norm_abcProfile_one (k : ℝ) (y : T3) : ‖abcProfile k 1 0 0 y‖ = 1 := by
  rw [abcProfile_apply, EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_three, Real.sin_sq_add_cos_sq]

/-- A path that is `0` for `t ≤ 0` and `t² · (unit Beltrami field of wavenumber t⁻³)` for
`t > 0`. Each `‖u(t, x)‖ ≤ t²`, so it is differentiable in `t` at `0` with derivative `0` at
every `x`, but its vorticity has size `t⁻¹`. -/
@[expose] public def escapePath : TimeDependentVelocity := fun t y =>
  (if 0 < t then t ^ 2 else 0) • abcProfile (t⁻¹ ^ 3) 1 0 0 y

public theorem escapePath_of_nonpos {t : ℝ} (ht : t ≤ 0) : escapePath t = 0 := by
  funext y
  simp [escapePath, not_lt.2 ht]

public theorem norm_escapePath_le (s : ℝ) (y : T3) : ‖escapePath s y‖ ≤ ‖s ^ 2‖ := by
  unfold escapePath
  rw [norm_smul, norm_abcProfile_one, mul_one]
  split_ifs <;> simp [sq_nonneg]

public theorem hasDerivAt_escapePath_zero (y : T3) :
    HasDerivAt (fun s => escapePath s y) 0 0 := by
  rw [hasDerivAt_iff_isLittleO]
  have h0 : escapePath 0 y = 0 := by rw [escapePath_of_nonpos le_rfl]; rfl
  have hO : (fun s : ℝ => escapePath s y) =O[𝓝 0] fun s : ℝ => s ^ 2 :=
    Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun s => by
      rw [one_mul]; exact norm_escapePath_le s y)
  have ho := hO.trans_isLittleO (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (n := 2) one_lt_two)
  simpa [h0] using ho

/-- `escapePath` is a local smooth physical solution on `[0, 0]` from `u₀ = 0`. -/
public theorem isLocalPhysicalSolution_escapePath (ν : ℝ) :
    IsLocalPhysicalSolution ν 0 0 escapePath (fun _ _ => 0) := by
  have hz : escapePath 0 = 0 := escapePath_of_nonpos le_rfl
  refine ⟨hz, ?_, ?_, ?_⟩
  · intro t ht x
    obtain rfl : t = 0 := le_antisymm ht.2 ht.1
    have hdt : time_deriv escapePath 0 x = 0 := (hasDerivAt_escapePath_zero x).deriv
    rw [hdt, hz, convective_zero x, pressureGradient_const 0 x, laplacian_zero x]
    exact ⟨by simp, div_zero_field x⟩
  · intro t ht
    obtain rfl : t = 0 := le_antisymm ht.2 ht.1
    rw [hz]; exact contDiff_const
  · refine ⟨?_, ?_, ?_, ?_, ⟨0, fun t ht => by rw [escapePath_of_nonpos ht, hz]; simp⟩⟩
    · intro t ht x
      obtain rfl : t = 0 := le_antisymm ht.2 ht.1
      exact (hasDerivAt_escapePath_zero x).differentiableAt
    · intro t ht
      obtain rfl : t = 0 := le_antisymm ht.2 ht.1
      rw [hz]; exact continuous_const
    · intro t ht
      obtain rfl : t = 0 := le_antisymm ht.2 ht.1
      rw [hz]; simp
    · intro t ht
      obtain rfl : t = 0 := le_antisymm ht.2 ht.1
      exact le_rfl

/-- For `t > 0` the vorticity supremum of `escapePath` is exactly `t⁻¹`. -/
public theorem vorticity_sup_norm_escapePath_pos {t : ℝ} (ht : 0 < t) :
    vorticity_sup_norm (vorticity (escapePath t)) = t⁻¹ := by
  have hcurl : ∀ x, ‖vorticity (escapePath t) x‖ = t⁻¹ := by
    intro x
    have hfun : escapePath t = fun y => (t ^ 2) • abcProfile (t⁻¹ ^ 3) 1 0 0 y := by
      funext y; simp [escapePath, ht]
    simp only [vorticity]
    rw [hfun, curl_smul, curl_abcProfile, norm_smul, norm_smul, norm_abcProfile_one]
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    field_simp
  unfold vorticity_sup_norm
  simp only [hcurl, ciSup_const]

/-- `vorticity_sup_norm` of `escapePath` at `t = 0` is `0`. -/
public theorem vorticity_sup_norm_escapePath_zero :
    vorticity_sup_norm (vorticity (escapePath 0)) = 0 := by
  rw [escapePath_of_nonpos le_rfl]
  exact FrohmanianTether.ClayStatements.vorticity_sup_norm_zero_field

/-- `t ↦ ‖ω(escapePath t)‖_∞` is not continuous, hence not differentiable, at `0`. -/
public theorem not_differentiableAt_vorticity_sup_norm_escapePath :
    ¬ DifferentiableAt ℝ (fun τ => vorticity_sup_norm (vorticity (escapePath τ))) 0 := by
  intro hd
  have hc := hd.continuousAt
  rw [ContinuousAt, vorticity_sup_norm_escapePath_zero] at hc
  have h1 : Tendsto (fun τ => vorticity_sup_norm (vorticity (escapePath τ))) (𝓝[>] 0) (𝓝 0) :=
    hc.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun τ => vorticity_sup_norm (vorticity (escapePath τ))) (𝓝[>] 0) atTop := by
    refine tendsto_inv_nhdsGT_zero.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact (vorticity_sup_norm_escapePath_pos hτ).symm
  exact not_tendsto_nhds_of_tendsto_atTop h2 0 h1

/-- **The 0.1.4 `LocalTetherRate` is false at `u₀ = 0`**, for every `ν`. -/
public theorem not_localTetherRateV014_zero (ν : ℝ) : ¬ LocalTetherRateV014 0 ν := by
  rintro ⟨C, κ'', _hC, _hκ, h⟩
  exact not_differentiableAt_vorticity_sup_norm_escapePath
    ((h 0 escapePath (fun _ _ => 0) (isLocalPhysicalSolution_escapePath ν)).1 0 ⟨le_rfl, le_rfl⟩)

/-- **The `hDI` binder of the 0.1.4 `frohmanian_tether_theorem` was unsatisfiable**, so that
theorem held vacuously. -/
public theorem not_forall_localTetherRateV014 :
    ¬ ∀ (u₀ : VelocityField) (ν : ℝ), LocalTetherRateV014 u₀ ν :=
  fun h => not_localTetherRateV014_zero 0 (h 0 0)

#print axioms vorticity_sup_norm_eq_zero_of_not_bddAbove
#print axioms localTetherBoundV014_constraint_free_of_unbounded
#print axioms exists_isLocalPhysicalSolution_zero_time
#print axioms not_localTetherBound_of_unbounded
#print axioms not_localTetherRate_of_unbounded
#print axioms isLocalPhysicalSolution_escapePath
#print axioms vorticity_sup_norm_escapePath_pos
#print axioms not_differentiableAt_vorticity_sup_norm_escapePath
#print axioms not_localTetherRateV014_zero
#print axioms not_forall_localTetherRateV014

end FrohmanianTether.TetherDefinitionAudit
