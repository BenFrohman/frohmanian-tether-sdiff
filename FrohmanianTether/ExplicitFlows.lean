/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import FrohmanianTether.ClayStatements

/-!
# Explicit exact Navier–Stokes solutions: decaying shear and ABC (Beltrami) flows

Two classical moving, nonzero exact solutions, checked against the repository's own equations
(`navier_stokes_eq`, hence `NS_PDE` and `NS_PDE_On` for every `T`):

* decaying shear `u = e^{-ν k² t} (a sin(k x₂), 0, 0)`, constant pressure
  (`shearFlow_navier_stokes`);
* decaying ABC flow `u = e^{-ν k² t} (A sin(k x₂) + C cos(k x₁), B sin(k x₀) + A cos(k x₂),
  C sin(k x₁) + B cos(k x₀))`, pressure `p = -|u|²/2` (`abcFlow_navier_stokes`), a curl
  eigenfield `∇ × u = k u` (`curl_abcProfile`).

Both come from one mechanism (`flow_navier_stokes`): a trigonometric profile `V` with
`ΔV = -k² V` (`laplacian_trigField`), `div V = 0`, and `(V·∇)V + ∇p₀ = 0`. For `t < 0` the time
factor is continued affinely, as `IsPhysicalNSSolutionOn` requires of every solution.

With `k = 2π m` both are global smooth `ℤ³`-periodic solutions in Fefferman's class
(`shearFlow_isPeriodicSmoothSolution`, `abcFlow_isPeriodicSmoothSolution`), so they are genuine
instances of the conclusion of `Clay_B_exact` for these particular data (`clay_B_instance_shear`,
`clay_B_instance_abc`); this is in no sense a proof of any Clay Millennium statement.

They are **not** `KatoLocalWitness`es, and no witness exists for their data:
`KatoLocalWitness` requires `Integrable (‖u₀‖²)` on ℝ³, which fails for every continuous nonzero
periodic field (`not_integrable_sq_of_periodic`, `isEmpty_katoLocalWitness_of_periodic`,
`isEmpty_katoLocalWitness_shear`, `isEmpty_katoLocalWitness_abc`). Consequently the ℝ³-class
hypotheses `LocalTetherBound`, `SmoothPhysicalUniqueness`, `BKMGlobalContinuation` hold only
*vacuously* at such data (`*_vacuous_of_periodic`); these are recorded as an audit, not as
discharges.
-/

open MeasureTheory NavierStokes3D
open scoped ContDiff

noncomputable section

namespace ExplicitFlows

/-- Scalar trigonometric pair `α sin(k y_j) + β cos(k y_l)`. -/
@[expose] public def tp (k α β : ℝ) (j l : Fin 3) (y : T3) : ℝ :=
  α * Real.sin (k * y j) + β * Real.cos (k * y l)

/-- Its "derivative shape" `α cos(k y_j) + β sin(k y_l)`. -/
@[expose] public def tq (k α β : ℝ) (j l : Fin 3) (y : T3) : ℝ :=
  α * Real.cos (k * y j) + β * Real.sin (k * y l)

theorem hasFDerivAt_coord (j : Fin 3) (x : T3) :
    HasFDerivAt (fun y : T3 => y j) (EuclideanSpace.proj j : T3 →L[ℝ] ℝ) x :=
  (EuclideanSpace.proj j : T3 →L[ℝ] ℝ).hasFDerivAt

public theorem hasFDerivAt_tp (k α β : ℝ) (j l : Fin 3) (x : T3) :
    HasFDerivAt (tp k α β j l)
      ((α * k * Real.cos (k * x j)) • (EuclideanSpace.proj j : T3 →L[ℝ] ℝ) -
        (β * k * Real.sin (k * x l)) • (EuclideanSpace.proj l : T3 →L[ℝ] ℝ)) x := by
  have h1 := ((Real.hasDerivAt_sin (k * x j)).comp_hasFDerivAt x
    ((hasFDerivAt_coord j x).const_mul k)).const_mul α
  have h2 := ((Real.hasDerivAt_cos (k * x l)).comp_hasFDerivAt x
    ((hasFDerivAt_coord l x).const_mul k)).const_mul β
  convert h1.add h2 using 1
  ext v
  simp [smul_eq_mul]
  ring

public theorem hasFDerivAt_tq (k α β : ℝ) (j l : Fin 3) (x : T3) :
    HasFDerivAt (tq k α β j l)
      ((-(α * k * Real.sin (k * x j))) • (EuclideanSpace.proj j : T3 →L[ℝ] ℝ) +
        (β * k * Real.cos (k * x l)) • (EuclideanSpace.proj l : T3 →L[ℝ] ℝ)) x := by
  have h1 := ((Real.hasDerivAt_cos (k * x j)).comp_hasFDerivAt x
    ((hasFDerivAt_coord j x).const_mul k)).const_mul α
  have h2 := ((Real.hasDerivAt_sin (k * x l)).comp_hasFDerivAt x
    ((hasFDerivAt_coord l x).const_mul k)).const_mul β
  convert h1.add h2 using 1
  ext v
  simp [smul_eq_mul]
  ring

/-- Kronecker delta as a real number. -/
@[expose] public def kd (a b : Fin 3) : ℝ := if a = b then 1 else 0

public theorem fderiv_tp_apply (k α β : ℝ) (j l : Fin 3) (x v : T3) :
    fderiv ℝ (tp k α β j l) x v =
      α * k * Real.cos (k * x j) * v j - β * k * Real.sin (k * x l) * v l := by
  rw [(hasFDerivAt_tp k α β j l x).fderiv]
  simp [smul_eq_mul]

public theorem fderiv_tq_apply (k α β : ℝ) (j l : Fin 3) (x v : T3) :
    fderiv ℝ (tq k α β j l) x v =
      -(α * k * Real.sin (k * x j)) * v j + β * k * Real.cos (k * x l) * v l := by
  rw [(hasFDerivAt_tq k α β j l x).fderiv]
  simp [smul_eq_mul]

public theorem single_apply_kd (i j : Fin 3) :
    (EuclideanSpace.single i (1 : ℝ) : T3) j = kd j i := by
  simp [kd]

/-- The directional derivative of `tp` in direction `eᵢ` is a `tq`. -/
public theorem fderiv_tp_single (k α β : ℝ) (j l i : Fin 3) :
    (fun y => fderiv ℝ (tp k α β j l) y (EuclideanSpace.single i 1)) =
      tq k (α * k * kd j i) (-(β * k * kd l i)) j l := by
  funext y
  rw [fderiv_tp_apply, single_apply_kd, single_apply_kd]
  simp only [tq]
  ring

public theorem contDiff_tp (k α β : ℝ) (j l : Fin 3) : ContDiff ℝ ∞ (tp k α β j l) := by
  have hj : ContDiff ℝ ∞ (fun y : T3 => y j) := (EuclideanSpace.proj j : T3 →L[ℝ] ℝ).contDiff
  have hl : ContDiff ℝ ∞ (fun y : T3 => y l) := (EuclideanSpace.proj l : T3 →L[ℝ] ℝ).contDiff
  unfold tp
  exact (contDiff_const.mul (Real.contDiff_sin.comp (contDiff_const.mul hj))).add
    (contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul hl)))

public theorem fderiv_tq_single_sum (k : ℝ) (j l : Fin 3) (x : T3) (a b : Fin 3 → ℝ) :
    ∑ i : Fin 3, fderiv ℝ (tq k (a i * kd j i) (b i * kd l i) j l) x
        (EuclideanSpace.single i 1) =
      -(a j * k * Real.sin (k * x j)) + b l * k * Real.cos (k * x l) := by
  simp only [fderiv_tq_apply, single_apply_kd]
  rw [Fin.sum_univ_three]
  fin_cases j <;> fin_cases l <;> simp [kd] <;> ring

/-- A velocity field whose `i`-th component is `tp k (α i) (β i) (j i) (l i)`. -/
@[expose] public def trigField (k : ℝ) (α β : Fin 3 → ℝ) (j l : Fin 3 → Fin 3) : VelocityField :=
  fun y => WithLp.toLp 2 (fun i => tp k (α i) (β i) (j i) (l i) y)

public theorem trigField_apply (k : ℝ) (α β : Fin 3 → ℝ) (j l : Fin 3 → Fin 3) (y : T3)
    (i : Fin 3) : trigField k α β j l y i = tp k (α i) (β i) (j i) (l i) y := rfl

public theorem contDiff_trigField (k : ℝ) (α β : Fin 3 → ℝ) (j l : Fin 3 → Fin 3) :
    ContDiff ℝ ∞ (trigField k α β j l) :=
  (contDiff_piLp (p := 2)).2 fun i => contDiff_tp k (α i) (β i) (j i) (l i)

public theorem div_trigField (k : ℝ) (α β : Fin 3 → ℝ) (j l : Fin 3 → Fin 3) (x : T3) :
    div (trigField k α β j l) x =
      ∑ i : Fin 3, (α i * k * Real.cos (k * x (j i)) * kd (j i) i -
        β i * k * Real.sin (k * x (l i)) * kd (l i) i) := by
  unfold div
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (fun y => trigField k α β j l y i) = tp k (α i) (β i) (j i) (l i) from rfl,
    fderiv_tp_apply, single_apply_kd, single_apply_kd]

public theorem convective_trigField (k : ℝ) (α β : Fin 3 → ℝ) (j l : Fin 3 → Fin 3) (x : T3)
    (i : Fin 3) :
    convective (trigField k α β j l) (trigField k α β j l) x i =
      α i * k * Real.cos (k * x (j i)) * trigField k α β j l x (j i) -
        β i * k * Real.sin (k * x (l i)) * trigField k α β j l x (l i) := by
  rw [convective_coord _ _ _ _ ((contDiff_trigField k α β j l).differentiable
    (by simp)).differentiableAt]
  exact fderiv_tp_apply _ _ _ _ _ _ _

public theorem laplacian_trigField (k : ℝ) (α β : Fin 3 → ℝ) (j l : Fin 3 → Fin 3) (x : T3) :
    laplacian (trigField k α β j l) x = (-k ^ 2) • trigField k α β j l x := by
  ext m
  rw [laplacian_coord _ _ _ ((contDiff_trigField k α β j l).contDiffAt.of_le
    (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))),
    smul_coord]
  have hdir : ∀ i, (fun y => directionalCoord (trigField k α β j l) m i y) =
      tq k ((α m * k) * kd (j m) i) ((-(β m * k)) * kd (l m) i) (j m) (l m) := by
    intro i
    have := fderiv_tp_single k (α m) (β m) (j m) (l m) i
    funext y
    have hy := congrFun this y
    simp only [directionalCoord]
    rw [show (fun y => trigField k α β j l y m) = tp k (α m) (β m) (j m) (l m) from rfl, hy]
    simp only [tq]
    ring
  simp_rw [hdir]
  rw [fderiv_tq_single_sum k (j m) (l m) x (fun _ => α m * k) (fun _ => -(β m * k))]
  rw [trigField_apply]
  simp only [tp]
  ring

/-! ## Time factor -/

/-- `e^{c t}` for `t ≥ 0`, continued affinely (`1 + c t`) for `t < 0`, as
`IsPhysicalNSSolutionOn` asks of every solution (its clause pins `u t = u 0 + t • v₀`, `t ≤ 0`). -/
@[expose] public def decay (c t : ℝ) : ℝ := if 0 ≤ t then Real.exp (c * t) else 1 + c * t

public theorem decay_of_nonneg {c t : ℝ} (ht : 0 ≤ t) : decay c t = Real.exp (c * t) :=
  if_pos ht

public theorem decay_zero (c : ℝ) : decay c 0 = 1 := by simp [decay]

public theorem decay_of_nonpos {c t : ℝ} (ht : t ≤ 0) : decay c t = 1 + c * t := by
  unfold decay
  split_ifs with h
  · have : t = 0 := le_antisymm ht h
    subst this; simp
  · rfl

public theorem decay_pos {c t : ℝ} (ht : 0 ≤ t) : 0 < decay c t := by
  rw [decay_of_nonneg ht]; exact Real.exp_pos _

theorem hasDerivAt_exp_mul (c t : ℝ) :
    HasDerivAt (fun s => Real.exp (c * s)) (c * Real.exp (c * t)) t := by
  have := (Real.hasDerivAt_exp (c * t)).comp t ((hasDerivAt_id t).const_mul c)
  convert this using 1
  simp [mul_comm]

/-- `decay c` is differentiable at every `t ≥ 0` (two-sided, also at `t = 0`). -/
public theorem hasDerivAt_decay (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (decay c) (c * decay c t) t := by
  rcases ht.lt_or_eq with ht | ht
  · have heq : (fun s => Real.exp (c * s)) =ᶠ[nhds t] decay c := by
      filter_upwards [lt_mem_nhds ht] with s hs
      exact (decay_of_nonneg hs.le).symm
    rw [decay_of_nonneg ht.le]
    exact (hasDerivAt_exp_mul c t).congr_of_eventuallyEq heq.symm
  · subst ht
    rw [decay_zero, mul_one]
    have h1 : HasDerivWithinAt (decay c) c (Set.Ici 0) 0 := by
      have := (hasDerivAt_exp_mul c 0).hasDerivWithinAt (s := Set.Ici 0)
      simp only [mul_zero, Real.exp_zero, mul_one] at this
      exact this.congr (fun s hs => decay_of_nonneg hs) (decay_of_nonneg le_rfl)
    have h2 : HasDerivWithinAt (decay c) c (Set.Iic 0) 0 := by
      have : HasDerivAt (fun s => 1 + c * s) c 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul c).const_add 1
      exact this.hasDerivWithinAt.congr (fun s hs => decay_of_nonpos hs)
        (decay_of_nonpos le_rfl)
    have := h2.union h1
    rwa [Set.Iic_union_Ici, hasDerivWithinAt_univ] at this

/-! ## The general mechanism: a stationary profile with balanced nonlinearity -/

/-- The decaying flow built from the profile `trigField k α β j l` and rate `ν k²`. -/
@[expose] public def flow (ν k : ℝ) (α β : Fin 3 → ℝ) (j l : Fin 3 → Fin 3) :
    TimeDependentVelocity :=
  fun t y => decay (-(ν * k ^ 2)) t • trigField k α β j l y

/-- Each time slice of `flow` is again a trig field (amplitudes scaled). -/
public theorem flow_eq_trigField (ν k : ℝ) (α β : Fin 3 → ℝ) (j l : Fin 3 → Fin 3) (t : ℝ) :
    flow ν k α β j l t =
      trigField k (fun i => decay (-(ν * k ^ 2)) t * α i)
        (fun i => decay (-(ν * k ^ 2)) t * β i) j l := by
  funext y
  ext i
  simp only [flow, smul_coord, trigField_apply, tp]
  ring

/-- The pressure `φ(t)² p₀`. -/
@[expose] public def flowPressure (ν k : ℝ) (p₀ : PressureField) : TimeDependentPressure :=
  fun t y => decay (-(ν * k ^ 2)) t ^ 2 * p₀ y

public theorem gradient_const_mul (a : ℝ) (p : PressureField) (hp : Differentiable ℝ p)
    (x : T3) : pressureGradient (fun y => a * p y) x = a • pressureGradient p x := by
  ext i
  simp only [pressureGradient]
  rw [smul_coord, gradient_coord _ _ _ ((hp x).const_mul a), gradient_coord _ _ _ (hp x),
    fderiv_const_mul (hp x)]
  rfl

public theorem time_deriv_flow (ν k : ℝ) (α β : Fin 3 → ℝ) (j l : Fin 3 → Fin 3) {t : ℝ}
    (ht : 0 ≤ t) (x : T3) :
    HasDerivAt (fun s => flow ν k α β j l s x)
      ((-(ν * k ^ 2)) • flow ν k α β j l t x) t := by
  have := (hasDerivAt_decay (-(ν * k ^ 2)) ht).smul_const (trigField k α β j l x)
  convert this using 1
  simp only [flow, smul_smul]

/-- **Master lemma.** If the profile `V` is divergence-free and its nonlinearity is balanced by
a differentiable pressure `p₀` (`(V·∇)V + ∇p₀ = 0`), then the decaying flow with pressure
`φ(t)² p₀` solves the repo's Navier–Stokes equations (`navier_stokes_eq`) for all `t ≥ 0`. -/
public theorem flow_navier_stokes (ν k : ℝ) (α β : Fin 3 → ℝ) (j l : Fin 3 → Fin 3)
    (p₀ : PressureField) (hp₀ : Differentiable ℝ p₀)
    (hdiv : ∀ x, div (trigField k α β j l) x = 0)
    (hbal : ∀ x, convective (trigField k α β j l) (trigField k α β j l) x +
      pressureGradient p₀ x = 0) :
    navier_stokes_eq (flow ν k α β j l) (flowPressure ν k p₀) ν := by
  intro t ht x
  set φ := decay (-(ν * k ^ 2)) t with hφ
  set V := trigField k α β j l with hV
  have hVd : Differentiable ℝ V :=
    (contDiff_trigField k α β j l).differentiable (by simp)
  have hut : flow ν k α β j l t = fun y => φ • V y := rfl
  refine ⟨?_, ?_⟩
  · have htd : time_deriv (flow ν k α β j l) t x = (-(ν * k ^ 2)) • (φ • V x) :=
      (time_deriv_flow ν k α β j l ht x).deriv
    have hconv : convective (flow ν k α β j l t) (flow ν k α β j l t) x =
        (φ ^ 2) • convective V V x := by
      rw [hut]
      simp only [convective]
      have hF : HasFDerivAt (fun y => φ • V y) (φ • fderiv ℝ V x) x :=
        (hVd x).hasFDerivAt.const_smul φ
      rw [hF.fderiv, ContinuousLinearMap.smul_apply, map_smul, smul_smul]
      ring_nf
    have hlap : laplacian (flow ν k α β j l t) x = (-k ^ 2) • (φ • V x) := by
      rw [flow_eq_trigField, laplacian_trigField, ← flow_eq_trigField]
      rfl
    have hpg : pressureGradient (flowPressure ν k p₀ t) x = (φ ^ 2) • pressureGradient p₀ x :=
      gradient_const_mul _ p₀ hp₀ x
    rw [htd, hconv, hlap, hpg]
    have hb := hbal x
    ext i
    have hbi := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v i) hb
    simp only [PiLp.add_apply, PiLp.zero_apply] at hbi
    simp only [PiLp.add_apply, smul_coord]
    linear_combination (φ ^ 2) * hbi
  · rw [hut, div_smul, hdiv, mul_zero]

/-! ## Decaying shear flow `u = e^{-ν k² t} (a sin(k x₂), 0, 0)` (coordinates `x₀, x₁, x₂`) -/

/-- Amplitudes of the shear profile `(a sin(k x₂), 0, 0)`. -/
@[expose] public def shearα (a : ℝ) : Fin 3 → ℝ := ![a, 0, 0]

/-- The shear profile `(a sin(k x₂), 0, 0)`. -/
@[expose] public def shearProfile (k a : ℝ) : VelocityField :=
  trigField k (shearα a) 0 (fun _ => 2) (fun _ => 2)

/-- The decaying shear flow `u(t, x) = e^{-ν k² t} (a sin(k x₂), 0, 0)` (for `t ≥ 0`). -/
@[expose] public def shearFlow (ν k a : ℝ) : TimeDependentVelocity :=
  flow ν k (shearα a) 0 (fun _ => 2) (fun _ => 2)

/-- Constant (zero) pressure for the shear flow. -/
@[expose] public def shearPressure : TimeDependentPressure := fun _ _ => 0

public theorem shearProfile_apply (k a : ℝ) (y : T3) :
    shearProfile k a y = WithLp.toLp 2 ![a * Real.sin (k * y 2), 0, 0] := by
  ext i
  fin_cases i <;> simp [shearProfile, trigField_apply, tp, shearα]

public theorem shearFlow_apply (ν k a : ℝ) {t : ℝ} (ht : 0 ≤ t) (y : T3) :
    shearFlow ν k a t y =
      WithLp.toLp 2 ![Real.exp (-(ν * k ^ 2) * t) * a * Real.sin (k * y 2), 0, 0] := by
  ext i
  fin_cases i <;> simp [shearFlow, flow, trigField_apply, tp, shearα, decay_of_nonneg ht]
  ring

public theorem div_shearProfile (k a : ℝ) (x : T3) : div (shearProfile k a) x = 0 := by
  rw [shearProfile, div_trigField, Fin.sum_univ_three]
  simp [shearα, kd]

public theorem convective_shearProfile (k a : ℝ) (x : T3) :
    convective (shearProfile k a) (shearProfile k a) x = 0 := by
  ext i
  rw [shearProfile, convective_trigField]
  simp [trigField_apply, tp, shearα]

/-- **The decaying shear flow solves Navier–Stokes** (`navier_stokes_eq`, all `t ≥ 0`) with
constant pressure, for every `ν, k, a`. -/
public theorem shearFlow_navier_stokes (ν k a : ℝ) :
    navier_stokes_eq (shearFlow ν k a) shearPressure ν := by
  have h := flow_navier_stokes ν k (shearα a) 0 (fun _ => 2) (fun _ => 2) (fun _ => 0)
    (differentiable_const 0) (div_shearProfile k a) (fun x => by
      have := convective_shearProfile k a x
      simp only [shearProfile] at this
      rw [this, zero_add]
      simpa using pressureGradient_const 0 x)
  have hp : flowPressure ν k (fun _ => (0 : ℝ)) = shearPressure := by
    funext t y; simp [flowPressure, shearPressure]
  rw [hp] at h
  exact h

public theorem shearFlow_NS_PDE (ν k a : ℝ) : NS_PDE (shearFlow ν k a) shearPressure ν :=
  shearFlow_navier_stokes ν k a

public theorem shearFlow_NS_PDE_On (ν k a T : ℝ) :
    NS_PDE_On (shearFlow ν k a) shearPressure ν T :=
  (shearFlow_NS_PDE ν k a).on T

/-! ## Decaying ABC (Arnold–Beltrami–Childress) flow -/

/-- ABC amplitudes: `u = (A sin(k x₂) + C cos(k x₁), B sin(k x₀) + A cos(k x₂),
C sin(k x₁) + B cos(k x₀))`. -/
@[expose] public def abcα (A B C : ℝ) : Fin 3 → ℝ := ![A, B, C]
@[expose] public def abcβ (A B C : ℝ) : Fin 3 → ℝ := ![C, A, B]
@[expose] public def abcj : Fin 3 → Fin 3 := ![2, 0, 1]
@[expose] public def abcl : Fin 3 → Fin 3 := ![1, 2, 0]

/-- The ABC profile. -/
@[expose] public def abcProfile (k A B C : ℝ) : VelocityField :=
  trigField k (abcα A B C) (abcβ A B C) abcj abcl

/-- The decaying ABC flow `e^{-ν k² t} · abcProfile` (for `t ≥ 0`). -/
@[expose] public def abcFlow (ν k A B C : ℝ) : TimeDependentVelocity :=
  flow ν k (abcα A B C) (abcβ A B C) abcj abcl

public theorem abcProfile_apply (k A B C : ℝ) (y : T3) :
    abcProfile k A B C y = WithLp.toLp 2
      ![A * Real.sin (k * y 2) + C * Real.cos (k * y 1),
        B * Real.sin (k * y 0) + A * Real.cos (k * y 2),
        C * Real.sin (k * y 1) + B * Real.cos (k * y 0)] := by
  ext i
  fin_cases i <;> simp [abcProfile, trigField_apply, tp, abcα, abcβ, abcj, abcl]

/-- Profile pressure `p₀ = -(u₀² + u₁² + u₂²)/2`, i.e. `-|u|²/2` (`abcPressure₀_eq_norm`). -/
@[expose] public def abcPressure₀ (k A B C : ℝ) : PressureField := fun y =>
  -((abcProfile k A B C y 0) ^ 2 + (abcProfile k A B C y 1) ^ 2 +
    (abcProfile k A B C y 2) ^ 2) / 2

public theorem abcPressure₀_eq_norm (k A B C : ℝ) (y : T3) :
    abcPressure₀ k A B C y = -‖abcProfile k A B C y‖ ^ 2 / 2 := by
  rw [abcPressure₀, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp [Real.norm_eq_abs, sq_abs]

/-- The ABC pressure `p(t) = φ(t)² p₀ = -|u(t)|²/2`. -/
@[expose] public def abcPressure (ν k A B C : ℝ) : TimeDependentPressure :=
  flowPressure ν k (abcPressure₀ k A B C)

public theorem div_abcProfile (k A B C : ℝ) (x : T3) : div (abcProfile k A B C) x = 0 := by
  rw [abcProfile, div_trigField, Fin.sum_univ_three]
  simp [abcj, abcl, kd]

theorem hasFDerivAt_abcPressure₀ (k A B C : ℝ) (x : T3) :
    HasFDerivAt (abcPressure₀ k A B C)
      (-(abcProfile k A B C x 0 • fderiv ℝ (tp k A C 2 1) x +
        abcProfile k A B C x 1 • fderiv ℝ (tp k B A 0 2) x +
        abcProfile k A B C x 2 • fderiv ℝ (tp k C B 1 0) x)) x := by
  have e : ∀ y, abcProfile k A B C y 0 = tp k A C 2 1 y ∧
      abcProfile k A B C y 1 = tp k B A 0 2 y ∧ abcProfile k A B C y 2 = tp k C B 1 0 y :=
    fun y => ⟨rfl, rfl, rfl⟩
  have d0 := (hasFDerivAt_tp k A C 2 1 x)
  have d1 := (hasFDerivAt_tp k B A 0 2 x)
  have d2 := (hasFDerivAt_tp k C B 1 0 x)
  have h := (((d0.mul d0).add (d1.mul d1)).add (d2.mul d2)).const_mul (-(1 / 2 : ℝ))
  rw [d0.fderiv, d1.fderiv, d2.fderiv]
  convert h using 1
  · funext y
    simp only [abcPressure₀, (e y).1, (e y).2.1, (e y).2.2, Pi.add_apply, Pi.mul_apply]
    ring
  · ext v
    simp only [(e x).1, (e x).2.1, (e x).2.2]
    simp [smul_eq_mul]
    ring

public theorem differentiable_abcPressure₀ (k A B C : ℝ) :
    Differentiable ℝ (abcPressure₀ k A B C) :=
  fun x => (hasFDerivAt_abcPressure₀ k A B C x).differentiableAt

/-- **Beltrami balance**: `(u·∇)u + ∇p₀ = 0` for the ABC profile with `p₀ = -|u|²/2`. -/
public theorem abc_balance (k A B C : ℝ) (x : T3) :
    convective (abcProfile k A B C) (abcProfile k A B C) x +
      pressureGradient (abcPressure₀ k A B C) x = 0 := by
  ext i
  simp only [PiLp.add_apply, PiLp.zero_apply, pressureGradient]
  rw [gradient_coord _ _ _ (differentiable_abcPressure₀ k A B C x),
    (hasFDerivAt_abcPressure₀ k A B C x).fderiv, abcProfile, convective_trigField]
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, fderiv_tp_apply, single_apply_kd]
  fin_cases i <;> simp [trigField_apply, tp, abcα, abcβ, abcj, abcl, kd] <;> ring

/-- **The decaying ABC flow solves Navier–Stokes** (`navier_stokes_eq`, all `t ≥ 0`) with
pressure `-|u|²/2`, for every `ν, k, A, B, C`. -/
public theorem abcFlow_navier_stokes (ν k A B C : ℝ) :
    navier_stokes_eq (abcFlow ν k A B C) (abcPressure ν k A B C) ν :=
  flow_navier_stokes ν k _ _ _ _ _ (differentiable_abcPressure₀ k A B C)
    (div_abcProfile k A B C) (abc_balance k A B C)

public theorem abcFlow_NS_PDE (ν k A B C : ℝ) :
    NS_PDE (abcFlow ν k A B C) (abcPressure ν k A B C) ν :=
  abcFlow_navier_stokes ν k A B C

public theorem abcFlow_NS_PDE_On (ν k A B C T : ℝ) :
    NS_PDE_On (abcFlow ν k A B C) (abcPressure ν k A B C) ν T :=
  (abcFlow_NS_PDE ν k A B C).on T

/-! ## Smoothness, periodicity, non-triviality -/

public theorem flow_smooth (ν k : ℝ) (α β : Fin 3 → ℝ) (j l : Fin 3 → Fin 3) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (flow ν k α β j l t) := by
  rw [flow_eq_trigField]; exact contDiff_trigField _ _ _ _ _

public theorem flow_zero (ν k : ℝ) (α β : Fin 3 → ℝ) (j l : Fin 3 → Fin 3) :
    flow ν k α β j l 0 = trigField k α β j l := by
  funext y; simp [flow, decay_zero]

public theorem latticeVec_apply (n : Fin 3 → ℤ) (j : Fin 3) :
    FrohmanianTether.ClayStatements.latticeVec n j = n j := by
  unfold FrohmanianTether.ClayStatements.latticeVec
  rw [Fin.sum_univ_three]
  fin_cases j <;> simp

/-- With `k = 2π m` (`m : ℤ`), every trig pair is `ℤ³`-periodic. -/
public theorem tp_periodic (m : ℤ) (α β : ℝ) (j l : Fin 3) (n : Fin 3 → ℤ) (y : T3) :
    tp (2 * Real.pi * m) α β j l (y + FrohmanianTether.ClayStatements.latticeVec n) =
      tp (2 * Real.pi * m) α β j l y := by
  simp only [tp, PiLp.add_apply, latticeVec_apply]
  have hs : 2 * Real.pi * m * (y j + n j) = 2 * Real.pi * m * y j + ((m * n j : ℤ) : ℝ) *
      (2 * Real.pi) := by push_cast; ring
  have hc : 2 * Real.pi * m * (y l + n l) = 2 * Real.pi * m * y l + ((m * n l : ℤ) : ℝ) *
      (2 * Real.pi) := by push_cast; ring
  rw [hs, hc, Real.sin_add_int_mul_two_pi, Real.cos_add_int_mul_two_pi]

public theorem trigField_periodic (m : ℤ) (α β : Fin 3 → ℝ) (j l : Fin 3 → Fin 3) :
    FrohmanianTether.ClayStatements.IsZ3Periodic (trigField (2 * Real.pi * m) α β j l) := by
  intro n y
  ext i
  simp only [trigField_apply, tp_periodic]

public theorem flow_periodic (ν : ℝ) (m : ℤ) (α β : Fin 3 → ℝ) (j l : Fin 3 → Fin 3) (t : ℝ) :
    FrohmanianTether.ClayStatements.IsZ3Periodic (flow ν (2 * Real.pi * m) α β j l t) := by
  rw [flow_eq_trigField]; exact trigField_periodic _ _ _ _ _

/-- **Physical clauses that do hold**: time-differentiability on `[0, T]`, continuity, and the
affine extension to `t ≤ 0`. (The remaining clause, finite energy on ℝ³, fails for every nonzero
periodic field: `not_integrable_sq_of_periodic`.) -/
public theorem flow_physical_clauses (ν k : ℝ) (α β : Fin 3 → ℝ) (j l : Fin 3 → Fin 3) (T : ℝ) :
    (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : T3, DifferentiableAt ℝ (fun s => flow ν k α β j l s x) t) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) T, Continuous (flow ν k α β j l t)) ∧
    (∃ v₀ : VelocityField, ∀ t ≤ (0 : ℝ),
      flow ν k α β j l t = flow ν k α β j l 0 + t • v₀) := by
  refine ⟨fun t ht x => (time_deriv_flow ν k α β j l ht.1 x).differentiableAt,
    fun t _ => (flow_smooth ν k α β j l t).continuous, ⟨fun y => (-(ν * k ^ 2)) •
      trigField k α β j l y, fun t ht => ?_⟩⟩
  funext y
  simp only [flow, decay_of_nonpos ht, decay_zero, Pi.add_apply, Pi.smul_apply, smul_smul,
    one_smul, add_smul]
  ring_nf

/-! ## Clay periodic class: the explicit flows are global smooth periodic solutions -/

/-- **Master lemma, periodic class.** Under the hypotheses of `flow_navier_stokes`, with
`k = 2π m`, a smooth periodic `p₀`, the decaying flow is an `IsPeriodicSmoothSolution`
(Fefferman's classical smooth periodic class, forcing `0`) from the profile. -/
public theorem flow_isPeriodicSmoothSolution (ν : ℝ) (m : ℤ) (α β : Fin 3 → ℝ)
    (j l : Fin 3 → Fin 3) (p₀ : PressureField) (hp₀ : ContDiff ℝ ∞ p₀)
    (hp₀per : FrohmanianTether.ClayStatements.IsZ3Periodic p₀)
    (hdiv : ∀ x, div (trigField (2 * Real.pi * m) α β j l) x = 0)
    (hbal : ∀ x, convective (trigField (2 * Real.pi * m) α β j l)
      (trigField (2 * Real.pi * m) α β j l) x + pressureGradient p₀ x = 0) :
    FrohmanianTether.ClayStatements.IsPeriodicSmoothSolution ν (trigField (2 * Real.pi * m) α β j l)
      (fun _ _ => 0) (flow ν (2 * Real.pi * m) α β j l)
      (flowPressure ν (2 * Real.pi * m) p₀) := by
  set k := 2 * Real.pi * m
  set c := -(ν * k ^ 2)
  have hNS := flow_navier_stokes ν k α β j l p₀ (hp₀.differentiable (by simp)) hdiv hbal
  have hexp : ContDiff ℝ ∞ (fun q : ℝ × T3 => Real.exp (c * q.1)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_fst)
  refine ⟨?_, ?_, ?_, flow_zero ν k α β j l, fun t _ => ⟨flow_periodic ν m α β j l t, ?_⟩⟩
  · refine (hexp.smul ((contDiff_trigField k α β j l).comp contDiff_snd)).contDiffOn.congr ?_
    rintro ⟨t, y⟩ ⟨ht, -⟩
    simp [flow, decay_of_nonneg (show (0 : ℝ) ≤ t from ht), c, neg_mul]
  · refine ((hexp.pow 2).mul (hp₀.comp contDiff_snd)).contDiffOn.congr ?_
    rintro ⟨t, y⟩ ⟨ht, -⟩
    simp [flowPressure, decay_of_nonneg (show (0 : ℝ) ≤ t from ht), c]
  · intro t ht x
    obtain ⟨h1, h2⟩ := hNS t ht x
    refine ⟨?_, h2⟩
    have hd : derivWithin (fun s => flow ν k α β j l s x) (Set.Ici 0) t =
        time_deriv (flow ν k α β j l) t x :=
      ((time_deriv_flow ν k α β j l ht x).hasDerivWithinAt.derivWithin
        (uniqueDiffOn_Ici 0 t ht)).trans (time_deriv_flow ν k α β j l ht x).deriv.symm
    show _ = _ + 0
    rw [hd, add_zero]
    exact h1
  · intro n y
    simp only [flowPressure, hp₀per n y]

/-- The decaying shear flow (`k = 2π m`) is a global smooth periodic solution in Fefferman's
class (`IsPeriodicSmoothSolution`, forcing `0`) from the profile `(a sin(2π m x₂), 0, 0)`. -/
public theorem shearFlow_isPeriodicSmoothSolution (ν : ℝ) (m : ℤ) (a : ℝ) :
    FrohmanianTether.ClayStatements.IsPeriodicSmoothSolution ν
      (shearProfile (2 * Real.pi * m) a) (fun _ _ => 0)
      (shearFlow ν (2 * Real.pi * m) a) shearPressure := by
  have h := flow_isPeriodicSmoothSolution ν m (shearα a) 0 (fun _ => 2) (fun _ => 2)
    (fun _ => 0) contDiff_const (fun _ _ => rfl) (div_shearProfile _ a) (fun x => by
      have := convective_shearProfile (2 * Real.pi * m) a x
      simp only [shearProfile] at this
      rw [this, zero_add]
      simpa using pressureGradient_const 0 x)
  have hp : flowPressure ν (2 * Real.pi * m) (fun _ => (0 : ℝ)) = shearPressure := by
    funext t y; simp [flowPressure, shearPressure]
  rw [hp] at h
  exact h

public theorem contDiff_abcPressure₀ (k A B C : ℝ) : ContDiff ℝ ∞ (abcPressure₀ k A B C) := by
  have h := ((((contDiff_tp k A C 2 1).pow 2).add ((contDiff_tp k B A 0 2).pow 2)).add
    ((contDiff_tp k C B 1 0).pow 2)).neg.div_const 2
  exact h

public theorem abcPressure₀_periodic (m : ℤ) (A B C : ℝ) :
    FrohmanianTether.ClayStatements.IsZ3Periodic (abcPressure₀ (2 * Real.pi * m) A B C) := by
  intro n y
  unfold abcPressure₀ abcProfile
  rw [trigField_periodic]

/-- The decaying ABC flow (`k = 2π m`) is a global smooth periodic solution in Fefferman's class
(`IsPeriodicSmoothSolution`, forcing `0`) from the ABC profile, with pressure `-|u|²/2`. -/
public theorem abcFlow_isPeriodicSmoothSolution (ν : ℝ) (m : ℤ) (A B C : ℝ) :
    FrohmanianTether.ClayStatements.IsPeriodicSmoothSolution ν
      (abcProfile (2 * Real.pi * m) A B C) (fun _ _ => 0)
      (abcFlow ν (2 * Real.pi * m) A B C) (abcPressure ν (2 * Real.pi * m) A B C) :=
  flow_isPeriodicSmoothSolution ν m _ _ _ _ _ (contDiff_abcPressure₀ _ A B C)
    (abcPressure₀_periodic m A B C) (div_abcProfile _ A B C) (abc_balance _ A B C)

/-- **Non-triviality (shear).** For `a ≠ 0`, `k ≠ 0` and `t ≥ 0`, the shear flow is nonzero:
at a point with `k x₂ = π/2` its first component is `e^{-ν k² t} a`. -/
public theorem shearFlow_ne_zero (ν : ℝ) {k a : ℝ} (hk : k ≠ 0) (ha : a ≠ 0) {t : ℝ}
    (ht : 0 ≤ t) : shearFlow ν k a t ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : VelocityField => v (EuclideanSpace.single 2 (Real.pi / (2 * k))) 0) h
  simp only [shearFlow_apply ν k a ht] at h0
  simp [Real.exp_ne_zero, ha] at h0
  rw [show k * (Real.pi / (2 * k)) = Real.pi / 2 by field_simp, Real.sin_pi_div_two] at h0
  norm_num at h0

/-- **Non-triviality (ABC).** At the origin the ABC flow is `e^{-ν k² t} (C, A, B)`; so it is
nonzero for `t ≥ 0` unless `A = B = C = 0`. -/
public theorem abcFlow_apply_zero (ν k A B C : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    abcFlow ν k A B C t 0 = Real.exp (-(ν * k ^ 2) * t) • WithLp.toLp 2 ![C, A, B] := by
  simp only [abcFlow, flow, decay_of_nonneg ht]
  congr 1
  rw [← abcProfile, abcProfile_apply]
  simp

public theorem abcFlow_ne_zero (ν k : ℝ) {A B C : ℝ} (hABC : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) {t : ℝ}
    (ht : 0 ≤ t) : abcFlow ν k A B C t ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  rw [abcFlow_apply_zero ν k A B C ht] at h0
  have hv : (WithLp.toLp 2 ![C, A, B] : EuclideanSpace ℝ (Fin 3)) = 0 :=
    (smul_eq_zero.mp h0).resolve_left (Real.exp_ne_zero _)
  have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) hv
  have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) hv
  have h3 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) hv
  simp at h1 h2 h3
  rcases hABC with hA | hB | hC
  · exact hA h2
  · exact hB h3
  · exact hC h1

/-- **Beltrami property**: the ABC profile is an eigenfield of the curl, `∇ × u = k u`. -/
public theorem curl_abcProfile (k A B C : ℝ) (x : T3) :
    curl (abcProfile k A B C) x = k • abcProfile k A B C x := by
  have hd : ∀ c d : Fin 3, directionalCoord (abcProfile k A B C) c d x =
      fderiv ℝ (tp k (abcα A B C c) (abcβ A B C c) (abcj c) (abcl c)) x
        (EuclideanSpace.single d 1) := fun _ _ => rfl
  ext i
  simp only [curl, hd, fderiv_tp_apply, single_apply_kd]
  fin_cases i <;>
    simp [abcα, abcβ, abcj, abcl, kd, abcProfile_apply] <;>
    ring

/-- A global smooth periodic solution restricts to one on `[0, T)`. -/
public theorem isPeriodicSmoothSolutionOn_of_global {ν T : ℝ} {u₀ : VelocityField}
    {u : TimeDependentVelocity} {p : TimeDependentPressure}
    (h : FrohmanianTether.ClayStatements.IsPeriodicSmoothSolution ν u₀ (fun _ _ => 0) u p) :
    FrohmanianTether.ClayStatements.IsPeriodicSmoothSolutionOn ν T u₀ u p := by
  obtain ⟨hu, hp, hNS, h0, hper⟩ := h
  have hsub : Set.Ico (0 : ℝ) T ×ˢ (Set.univ : Set T3) ⊆ Set.Ici 0 ×ˢ Set.univ :=
    Set.prod_mono Set.Ico_subset_Ici_self le_rfl
  refine ⟨hu.mono hsub, hp.mono hsub, fun t ht x => ?_, h0, fun t ht => hper t ht.1⟩
  obtain ⟨h1, h2⟩ := hNS t ht.1 x
  exact ⟨by simpa using h1, h2⟩

/-! ## Why no nonzero periodic field can be a `KatoLocalWitness` -/

theorem latticeVec_single0 (n : ℤ) :
    FrohmanianTether.ClayStatements.latticeVec (Pi.single 0 n) =
      (n : ℝ) • EuclideanSpace.single 0 (1 : ℝ) := by
  ext j
  rw [latticeVec_apply]
  fin_cases j <;> simp

/-- **Infinite energy.** A continuous, `ℤ³`-periodic, not identically zero field on ℝ³ does not
have `‖u‖²` integrable: the set where `‖u‖² ≥ c > 0` contains infinitely many disjoint
translates of a ball. -/
public theorem not_integrable_sq_of_periodic {u : VelocityField} (hc : Continuous u)
    (hp : FrohmanianTether.ClayStatements.IsZ3Periodic u) (hne : u ≠ 0) :
    ¬ Integrable (fun x => ‖u x‖ ^ 2) := by
  intro hint
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, u x₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  set g : T3 → ℝ := fun x => ‖u x‖ ^ 2 with hg
  have hg0 : 0 < g x₀ := by simp only [g]; positivity
  set c : ℝ := g x₀ / 2 with hcdef
  have hc0 : 0 < c := by positivity
  have hgc : Continuous g := hc.norm.pow 2
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, Metric.ball x₀ r ⊆ {x | c < g x} :=
    Metric.isOpen_iff.mp (isOpen_lt continuous_const hgc) x₀ (by
      show c < g x₀
      linarith)
  set r' := min r (1 / 2) with hr'def
  have hr' : 0 < r' := lt_min hr (by norm_num)
  set v : ℤ → T3 := fun n => (n : ℝ) • EuclideanSpace.single 0 (1 : ℝ) with hv
  set B : ℤ → Set T3 := fun n => Metric.ball (x₀ + v n) r' with hB
  have hsub : (⋃ n, B n) ⊆ {x | c ≤ ‖g x‖} := by
    intro y hy
    obtain ⟨n, hy⟩ := Set.mem_iUnion.mp hy
    have hy' : y - v n ∈ Metric.ball x₀ r := by
      have h1 : dist (y - v n) x₀ < r' := by
        have e : y - v n - x₀ = y - (x₀ + v n) := by abel
        rw [dist_eq_norm, e, ← dist_eq_norm]
        exact hy
      exact lt_of_lt_of_le h1 (min_le_left _ _)
    have hper : g y = g (y - v n) := by
      have := hp (Pi.single 0 n) (y - v n)
      rw [latticeVec_single0, sub_add_cancel] at this
      simp only [g, this]
    have := hball hy'
    simp only [Set.mem_setOf_eq] at this ⊢
    rw [Real.norm_of_nonneg (by simp only [g]; positivity), hper]
    exact this.le
  have hdisj : Pairwise (Function.onFun Disjoint B) := by
    intro n m hnm
    apply Metric.ball_disjoint_ball
    rw [dist_eq_norm]
    have e : x₀ + v n - (x₀ + v m) = ((n - m : ℤ) : ℝ) • EuclideanSpace.single 0 (1 : ℝ) := by
      simp only [v, Int.cast_sub, sub_smul]
      abel
    rw [e, norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
    have h1 : (1 : ℝ) ≤ |((n - m : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hnm)
    have h2 : r' ≤ 1 / 2 := min_le_right _ _
    linarith
  have hmeas : MeasureTheory.volume (⋃ n, B n) = ⊤ := by
    rw [measure_iUnion hdisj (fun n => measurableSet_ball)]
    have : ∀ n, MeasureTheory.volume (B n) =
        MeasureTheory.volume (Metric.ball (0 : T3) r') := fun n =>
      Measure.addHaar_ball_center MeasureTheory.volume _ r'
    simp_rw [this]
    exact ENNReal.tsum_const_eq_top_of_ne_zero (Metric.measure_ball_pos MeasureTheory.volume 0 hr').ne'
  have hfin := hint.measure_norm_ge_lt_top hc0
  have := (measure_mono hsub).trans_lt hfin
  rw [hmeas] at this
  exact lt_irrefl _ this

/-- Hence a nonzero periodic initial field admits no solution with `IsPhysicalNSSolutionOn`. -/
public theorem not_isPhysicalNSSolutionOn_of_periodic {u : TimeDependentVelocity} {T : ℝ}
    (hT : 0 ≤ T) (hp : FrohmanianTether.ClayStatements.IsZ3Periodic (u 0)) (hne : u 0 ≠ 0) :
    ¬ IsPhysicalNSSolutionOn u T := fun h =>
  not_integrable_sq_of_periodic (h.2.1 0 ⟨le_rfl, hT⟩) hp hne (h.2.2.1 0 ⟨le_rfl, hT⟩)

/-- **No Kato witness for nonzero periodic data**: `KatoLocalWitness u₀ ν` is empty whenever
`u₀` is `ℤ³`-periodic and not identically zero (finite energy on ℝ³ is part of the witness). -/
public theorem isEmpty_katoLocalWitness_of_periodic {u₀ : VelocityField} {ν : ℝ}
    (hp : FrohmanianTether.ClayStatements.IsZ3Periodic u₀) (hne : u₀ ≠ 0) :
    IsEmpty (KatoLocalWitness u₀ ν) :=
  ⟨fun w => not_isPhysicalNSSolutionOn_of_periodic w.Tpos.le (by rw [w.init]; exact hp)
    (by rw [w.init]; exact hne) w.phys⟩

public theorem shearProfile_ne_zero {m : ℤ} (hm : m ≠ 0) {a : ℝ} (ha : a ≠ 0) :
    shearProfile (2 * Real.pi * m) a ≠ 0 := by
  have hk : (2 * Real.pi * m : ℝ) ≠ 0 := by
    have := Real.pi_ne_zero
    have : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    positivity
  have h := shearFlow_ne_zero 0 hk ha (le_refl (0 : ℝ))
  rwa [shearFlow, flow_zero] at h

public theorem abcProfile_ne_zero (k : ℝ) {A B C : ℝ} (hABC : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) :
    abcProfile k A B C ≠ 0 := by
  have h := abcFlow_ne_zero 0 k hABC (le_refl (0 : ℝ))
  rwa [abcFlow, flow_zero] at h

/-- The shear flow is **not** a `KatoLocalWitness` (for any `ν`): none exists for its data. -/
public theorem isEmpty_katoLocalWitness_shear (ν : ℝ) {m : ℤ} (hm : m ≠ 0) {a : ℝ}
    (ha : a ≠ 0) : IsEmpty (KatoLocalWitness (shearProfile (2 * Real.pi * m) a) ν) :=
  isEmpty_katoLocalWitness_of_periodic
    (by rw [shearProfile]; exact trigField_periodic _ _ _ _ _) (shearProfile_ne_zero hm ha)

/-- The ABC flow is **not** a `KatoLocalWitness` (for any `ν`): none exists for its data. -/
public theorem isEmpty_katoLocalWitness_abc (ν : ℝ) (m : ℤ) {A B C : ℝ}
    (hABC : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) :
    IsEmpty (KatoLocalWitness (abcProfile (2 * Real.pi * m) A B C) ν) :=
  isEmpty_katoLocalWitness_of_periodic
    (by rw [abcProfile]; exact trigField_periodic _ _ _ _ _) (abcProfile_ne_zero _ hABC)

/-! ## Audit: the ℝ³-class hypotheses are *vacuous* at nonzero periodic data

These are recorded so that nobody mistakes them for discharges: at such `u₀` there is no
`IsLocalPhysicalSolution` on any `[0, T]` with `T ≥ 0`, so every binder quantifying over those
solutions holds trivially and `BKMGlobalContinuation`'s premise is false. -/

theorem not_isLocalPhysicalSolution_of_periodic {ν T : ℝ} {u₀ : VelocityField}
    {u : TimeDependentVelocity} {p : TimeDependentPressure} (hT : 0 ≤ T)
    (hp : FrohmanianTether.ClayStatements.IsZ3Periodic u₀) (hne : u₀ ≠ 0) :
    ¬ IsLocalPhysicalSolution ν T u₀ u p := fun hu =>
  not_isPhysicalNSSolutionOn_of_periodic hT (by rw [hu.1]; exact hp) (by rw [hu.1]; exact hne)
    hu.2.2.2

/-- VACUOUS (not a discharge): `LocalTetherBound` holds trivially at nonzero periodic data. -/
public theorem localTetherBound_vacuous_of_periodic {u₀ : VelocityField} {ν : ℝ}
    (hp : FrohmanianTether.ClayStatements.IsZ3Periodic u₀) (hne : u₀ ≠ 0) :
    TetheredLyapunov.LocalTetherBound u₀ ν := by
  refine ⟨0, fun T u p hu t ht => ?_⟩
  exact absurd hu (not_isLocalPhysicalSolution_of_periodic (ht.1.trans ht.2) hp hne)

/-- VACUOUS (not a discharge): `SmoothPhysicalUniqueness` holds trivially at nonzero periodic
data. -/
public theorem smoothPhysicalUniqueness_vacuous_of_periodic {u₀ : VelocityField} {ν : ℝ}
    (hp : FrohmanianTether.ClayStatements.IsZ3Periodic u₀) (hne : u₀ ≠ 0) :
    TetheredLyapunov.SmoothPhysicalUniqueness u₀ ν := fun _T _ _ _ _ hu _ _t ht =>
  absurd hu (not_isLocalPhysicalSolution_of_periodic (ht.1.trans ht.2) hp hne)

/-- VACUOUS (not a discharge): `BKMGlobalContinuation` holds trivially at nonzero periodic data,
because its `Nonempty (KatoLocalWitness u₀ ν)` premise is false. -/
public theorem bkmGlobalContinuation_vacuous_of_periodic {u₀ : VelocityField} {ν : ℝ}
    (hp : FrohmanianTether.ClayStatements.IsZ3Periodic u₀) (hne : u₀ ≠ 0) :
    TetheredLyapunov.BKMGlobalContinuation u₀ ν := fun ⟨w⟩ _ =>
  ((isEmpty_katoLocalWitness_of_periodic (ν := ν) hp hne).false w).elim

/-! ## Periodic (𝕋³) chain: genuine, non-vacuous instances -/

/-- The shear profile satisfies every hypothesis of `Clay_B_exact` and its conclusion: a global
smooth periodic solution exists (the explicit decaying shear flow). -/
public theorem clay_B_instance_shear (ν : ℝ) (m : ℤ) (a : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (shearProfile (2 * Real.pi * m) a) ∧
    (∀ x, div (shearProfile (2 * Real.pi * m) a) x = 0) ∧
    FrohmanianTether.ClayStatements.IsZ3Periodic (shearProfile (2 * Real.pi * m) a) ∧
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      FrohmanianTether.ClayStatements.IsPeriodicSmoothSolution ν
        (shearProfile (2 * Real.pi * m) a) (fun _ _ => 0) u p :=
  ⟨contDiff_trigField _ _ _ _ _, div_shearProfile _ a, trigField_periodic _ _ _ _ _,
    _, _, shearFlow_isPeriodicSmoothSolution ν m a⟩

/-- The ABC profile satisfies every hypothesis of `Clay_B_exact` and its conclusion: a global
smooth periodic solution exists (the explicit decaying ABC flow). -/
public theorem clay_B_instance_abc (ν : ℝ) (m : ℤ) (A B C : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (abcProfile (2 * Real.pi * m) A B C) ∧
    (∀ x, div (abcProfile (2 * Real.pi * m) A B C) x = 0) ∧
    FrohmanianTether.ClayStatements.IsZ3Periodic (abcProfile (2 * Real.pi * m) A B C) ∧
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      FrohmanianTether.ClayStatements.IsPeriodicSmoothSolution ν
        (abcProfile (2 * Real.pi * m) A B C) (fun _ _ => 0) u p :=
  ⟨contDiff_trigField _ _ _ _ _, div_abcProfile _ A B C, trigField_periodic _ _ _ _ _,
    _, _, abcFlow_isPeriodicSmoothSolution ν m A B C⟩

/-- The binder of `PeriodicTetherClosingBound` / `PeriodicBKMContinuation` is non-vacuous at the
shear data: the shear flow is an `IsPeriodicSmoothSolutionOn` on every `[0, T)`. -/
public theorem shearFlow_isPeriodicSmoothSolutionOn (ν T : ℝ) (m : ℤ) (a : ℝ) :
    FrohmanianTether.ClayStatements.IsPeriodicSmoothSolutionOn ν T
      (shearProfile (2 * Real.pi * m) a) (shearFlow ν (2 * Real.pi * m) a) shearPressure :=
  isPeriodicSmoothSolutionOn_of_global (shearFlow_isPeriodicSmoothSolution ν m a)

/-- Same for the ABC data. -/
public theorem abcFlow_isPeriodicSmoothSolutionOn (ν T : ℝ) (m : ℤ) (A B C : ℝ) :
    FrohmanianTether.ClayStatements.IsPeriodicSmoothSolutionOn ν T
      (abcProfile (2 * Real.pi * m) A B C) (abcFlow ν (2 * Real.pi * m) A B C)
      (abcPressure ν (2 * Real.pi * m) A B C) :=
  isPeriodicSmoothSolutionOn_of_global (abcFlow_isPeriodicSmoothSolution ν m A B C)

/-- At the shear data the conclusion of `PeriodicBKMContinuation` holds outright (so that
hypothesis is not needed there). -/
public theorem periodicBKM_conclusion_shear (ν : ℝ) (m : ℤ) (a : ℝ) :
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      FrohmanianTether.ClayStatements.IsPeriodicSmoothSolution ν
        (shearProfile (2 * Real.pi * m) a) (fun _ _ => 0) u p :=
  (clay_B_instance_shear ν m a).2.2.2

public theorem periodicBKM_conclusion_abc (ν : ℝ) (m : ℤ) (A B C : ℝ) :
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      FrohmanianTether.ClayStatements.IsPeriodicSmoothSolution ν
        (abcProfile (2 * Real.pi * m) A B C) (fun _ _ => 0) u p :=
  (clay_B_instance_abc ν m A B C).2.2.2

end ExplicitFlows
