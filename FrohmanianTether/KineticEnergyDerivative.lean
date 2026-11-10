/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
module
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.OpenPos
public import FrohmanianTether.ArnoldGeometric
/-!
# The kinetic-energy functional derivative is not the velocity (refutation)

Earlier versions carried the hypothesis `PlanSteps.KineticEnergyDerivIsVelocity`,
`∀ ω, FunctionalDerivative KineticEnergyHamiltonian ω = velocity_from_vorticity ω` ("δH/δω = u").
It has been REMOVED, together with every theorem that assumed it, because it is false with the
definitions of this repository. This file proves the negation:

* `not_forall_functionalDerivative_kineticEnergy_eq_velocity` — the statement is false.
  Counterexample: `ω = 1_B e₁` and `2 ω`, `B` the open unit ball centred at `(0,2,0)`. Their
  `fderiv`-based divergence vanishes identically (a two-valued function has zero `fderiv`
  everywhere), so it lies in `CoadjointOrbit`; it is not differentiable, so it has no functional
  gradient and `FunctionalDerivative` returns `0`; but `BiotSavart ω 0 ≠ 0` (its third component
  is strictly negative).
* `not_unique_isGateauxRepresentative`, `not_unique_velocity_representative` — a Gâteaux
  representative is never unique (changing it at one point gives another), so the former
  "unique representative ⇒ δH = u" lemmas had hypotheses that can never hold. (These concern the
  legacy pointwise predicate `IsGateauxRepresentative`; the rebuilt `FunctionalDerivative` uses
  `L²` classes, where the gradient IS unique: `ArnoldGeometric.isFunctionalGradient_unique`.)

SCOPE. The refutation uses a non-smooth vorticity field, at which `FunctionalDerivative` is `0`. It does not by itself decide what the derivative is for
smooth fields. For the vorticity (L²) pairing used by `IsGateauxRepresentative`, the classical
formal answer is the vector stream function `ψ = BS* BS ω` (with `curl ψ = u`), not `u`; that
identity is NOT formalized here. What is formalized (in `ArnoldGeometric`) is the
velocity-pairing statement `isVelocityGateauxRepresentative_kineticEnergy_at`: in the pairing
`∫ ⟨δ, BS ε⟩` the representative of kinetic energy is `u`.
-/

@[expose] public section

namespace KineticEnergyDerivative

open ArnoldGeometric NavierStokes3D MeasureTheory Filter Topology


/-- A real function with values in `{0, a}` has zero Fréchet derivative everywhere. -/
theorem fderiv_eq_zero_of_two_valued {f : T3 → ℝ} {a : ℝ} (hf : ∀ y, f y = 0 ∨ f y = a)
    (x : T3) : fderiv ℝ f x = 0 := by
  by_cases hd : DifferentiableAt ℝ f x
  · have hc : ContinuousAt f x := hd.continuousAt
    by_cases ha : a = 0
    · have : f = fun _ => 0 := by
        funext y; rcases hf y with h | h <;> simp [h, ha]
      rw [this]; exact fderiv_const_apply 0
    · have hpos : 0 < |a| := abs_pos.mpr ha
      have hev : f =ᶠ[𝓝 x] fun _ => f x := by
        have := hc (Metric.ball_mem_nhds (f x) hpos)
        filter_upwards [this] with y hy
        rw [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hy
        rcases hf y with h1 | h1 <;> rcases hf x with h2 | h2
        · rw [h1, h2]
        · exfalso; rw [h1, h2, zero_sub, abs_neg] at hy; exact lt_irrefl _ hy
        · exfalso; rw [h1, h2, sub_zero] at hy; exact lt_irrefl _ hy
        · rw [h1, h2]
      rw [hev.fderiv_eq]
      exact fderiv_const_apply _
  · exact fderiv_zero_of_not_differentiableAt hd

/-- Indicator vorticity field `1_B · a`. -/
noncomputable def indField (B : Set T3) (a : EuclideanSpace ℝ (Fin 3)) : T3 → EuclideanSpace ℝ (Fin 3) :=
  B.indicator (fun _ => a)

theorem indField_coord (B : Set T3) (a : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) (y : T3) :
    indField B a y i = 0 ∨ indField B a y i = a i := by
  unfold indField
  by_cases hy : y ∈ B
  · right; simp [Set.indicator_of_mem hy]
  · left; simp [Set.indicator_of_notMem hy]

theorem div_indField (B : Set T3) (a : EuclideanSpace ℝ (Fin 3)) (x : T3) :
    div (indField B a) x = 0 := by
  unfold div
  apply Finset.sum_eq_zero
  intro i _
  rw [fderiv_eq_zero_of_two_valued (indField_coord B a i) x]
  rfl

/-- The indicator field as a point of `CoadjointOrbit` (its `div` vanishes identically). -/
noncomputable def indOrbit (B : Set T3) (a : EuclideanSpace ℝ (Fin 3)) : CoadjointOrbit :=
  ⟨indField B a, div_indField B a⟩


/-- Centre `p = (0, 2, 0)` of the ball carrying the counterexample vorticity. -/
noncomputable def ctr : T3 := EuclideanSpace.single 1 2

/-- `e₁ = (1, 0, 0)`. -/
noncomputable def e1 : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 1

theorem not_differentiableAt_indField (a : EuclideanSpace ℝ (Fin 3)) (ha : a 0 ≠ 0) :
    ¬ DifferentiableAt ℝ (fun y => indField (Metric.ball ctr 1) a y 0) (ctr + e1) := by
  intro hd
  set f := fun y => indField (Metric.ball ctr 1) a y 0
  have hc : ContinuousAt f (ctr + e1) := hd.continuousAt
  have hfx : f (ctr + e1) = 0 := by
    simp only [f, indField]
    rw [Set.indicator_of_notMem]
    · rfl
    · simp [Metric.mem_ball, dist_eq_norm, e1]
  have hpath : Tendsto (fun s : ℝ => ctr + e1 - s • e1) (𝓝[>] 0) (𝓝 (ctr + e1)) := by
    have : Continuous (fun s : ℝ => ctr + e1 - s • e1) := by fun_prop
    have h0 := this.tendsto 0
    simp only [zero_smul, sub_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have h1 := hc.tendsto.comp hpath
  have hev : (fun s : ℝ => a 0) =ᶠ[𝓝[>] 0] (f ∘ fun s : ℝ => ctr + e1 - s • e1) := by
    have hIoo : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT one_pos
    filter_upwards [hIoo] with s hs
    simp only [Function.comp, f, indField]
    rw [Set.indicator_of_mem]
    rw [Metric.mem_ball, dist_eq_norm]
    have : ctr + e1 - s • e1 - ctr = (1 - s) • e1 := by
      rw [sub_smul, one_smul]; abel
    rw [this, norm_smul, e1, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs,
      abs_of_pos (by linarith [hs.2])]
    linarith [hs.1]
  have h2 : Tendsto (f ∘ fun s : ℝ => ctr + e1 - s • e1) (𝓝[>] 0) (𝓝 (a 0)) :=
    tendsto_const_nhds.congr' hev
  have := tendsto_nhds_unique h1 h2
  rw [hfx] at this
  exact ha this.symm


/-- If some coordinate of `ω` fails to be differentiable somewhere, every field is a
Gâteaux representative of every functional at `ω` (the defining condition is vacuous). -/
theorem isGateauxRepresentative_of_not_differentiable (F : CoadjointOrbit → ℝ)
    (ω : CoadjointOrbit) (hnd : ¬ ∀ i x, DifferentiableAt ℝ (fun y => ω.val y i) x)
    (d : T3 → EuclideanSpace ℝ (Fin 3)) : IsGateauxRepresentative F ω d := by
  rw [isGateauxRepresentative_iff]
  intro ε hω
  exact absurd hω hnd

/-- At a non-differentiable orbit point, `FunctionalDerivative F ω = 0` for every `F`
(no functional gradient exists there: the orbit line `ω + t ε` is not defined). -/
theorem functionalDerivative_of_not_differentiable (F : CoadjointOrbit → ℝ)
    (ω : CoadjointOrbit) (hnd : ¬ ∀ i x, DifferentiableAt ℝ (fun y => ω.val y i) x) :
    FunctionalDerivative F ω = 0 :=
  functionalDerivative_eq_zero_of_not_regular hnd

theorem indField_smul (B : Set T3) (c : ℝ) (a : EuclideanSpace ℝ (Fin 3)) :
    indField B (c • a) = fun y => c • indField B a y := by
  funext y
  unfold indField
  by_cases hy : y ∈ B
  · simp [Set.indicator_of_mem hy]
  · simp [Set.indicator_of_notMem hy]


/-- `y ↦ cross e₁ y` as a linear map (hence continuous on the finite-dimensional space). -/
noncomputable def crossE1 : T3 →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun y := cross e1 y
  map_add' := cross_add_right e1
  map_smul' c y := cross_smul_right c e1 y

/-- Biot–Savart integrand at `x = 0` on the ball, before the indicator. -/
noncomputable def bsInt0 (y : T3) : EuclideanSpace ℝ (Fin 3) :=
  biotSavartKernel 0 y • cross e1 (0 - y)

theorem ne_zero_of_mem_closedBall {y : T3} (hy : y ∈ Metric.closedBall ctr 1) : y ≠ 0 := by
  rintro rfl
  rw [Metric.mem_closedBall, dist_eq_norm, zero_sub, norm_neg, ctr, PiLp.norm_single,
    Real.norm_eq_abs] at hy
  norm_num at hy

theorem one_lt_coord_of_mem_ball {y : T3} (hy : y ∈ Metric.ball ctr 1) : 1 < y 1 := by
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have h := PiLp.norm_apply_le (y - ctr) 1
  have : (y - ctr) 1 = y 1 - 2 := by simp [ctr]
  rw [this, Real.norm_eq_abs] at h
  have := neg_abs_le (y 1 - 2)
  linarith

theorem continuousOn_bsInt0 : ContinuousOn bsInt0 (Metric.closedBall ctr 1) := by
  intro y hy
  have hy0 := ne_zero_of_mem_closedBall hy
  apply ContinuousAt.continuousWithinAt
  have hK : (fun z : T3 => biotSavartKernel 0 z) =ᶠ[𝓝 y]
      fun z => (4 * Real.pi)⁻¹ * ‖(0 : T3) - z‖ ^ (-(3 : ℝ)) := by
    filter_upwards [isOpen_ne.mem_nhds hy0] with z hz
    exact biotSavartKernel_of_ne (Ne.symm hz)
  have hKc : ContinuousAt (fun z : T3 => biotSavartKernel 0 z) y := by
    refine ContinuousAt.congr ?_ hK.symm
    refine continuousAt_const.mul ?_
    refine ContinuousAt.rpow_const (by fun_prop) (Or.inl ?_)
    rw [zero_sub, norm_neg]; exact norm_ne_zero_iff.mpr hy0
  have hC : Continuous fun z : T3 => cross e1 (0 - z) :=
    (LinearMap.continuous_of_finiteDimensional crossE1).comp (by fun_prop)
  exact hKc.smul hC.continuousAt

theorem integrable_bsField0 :
    Integrable (fun y => biotSavartKernel 0 y • cross (indField (Metric.ball ctr 1) e1 y) (0 - y))
      NavierStokes3D.volume := by
  have hfun : (fun y => biotSavartKernel 0 y • cross (indField (Metric.ball ctr 1) e1 y) (0 - y))
      = (Metric.ball ctr 1).indicator bsInt0 := by
    funext y
    unfold indField bsInt0
    by_cases hy : y ∈ Metric.ball ctr 1
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy, cross]
  rw [hfun]
  have hcb : IntegrableOn bsInt0 (Metric.closedBall ctr 1) MeasureTheory.volume :=
    continuousOn_bsInt0.integrableOn_compact (isCompact_closedBall ctr 1)
  exact (hcb.mono_set Metric.ball_subset_closedBall).integrable_indicator Metric.isOpen_ball.measurableSet


theorem bsField0_coord2 (y : T3) :
    (biotSavartKernel 0 y • cross (indField (Metric.ball ctr 1) e1 y) (0 - y)) 2 =
      -(Metric.ball ctr 1).indicator (fun z => biotSavartKernel 0 z * z 1) y := by
  unfold indField
  by_cases hy : y ∈ Metric.ball ctr 1
  · simp only [Set.indicator_of_mem hy, PiLp.smul_apply, smul_eq_mul, (cross_coord _ _).2.2]
    simp [e1]
  · simp [Set.indicator_of_notMem hy, cross]

/-- The Biot–Savart velocity of the counterexample field is nonzero at the origin
(its third component is strictly negative). -/
theorem biotSavart_indField_ne_zero :
    BiotSavart (indField (Metric.ball ctr 1) e1) 0 ≠ 0 := by
  intro h0
  have hint := integrable_bsField0
  have hcomm := (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).integral_comp_comm hint
  have hBS : BiotSavart (indField (Metric.ball ctr 1) e1) 0 =
      ∫ y, biotSavartKernel 0 y • cross (indField (Metric.ball ctr 1) e1 y) (0 - y)
        ∂NavierStokes3D.volume := BiotSavart_apply _ 0
  rw [← hBS, h0, map_zero] at hcomm
  have hp : ∀ v : EuclideanSpace ℝ (Fin 3), EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3) v = v 2 :=
    fun _ => rfl
  simp only [hp, bsField0_coord2] at hcomm
  rw [integral_neg, neg_eq_zero] at hcomm
  set g := (Metric.ball ctr 1).indicator (fun z : T3 => biotSavartKernel 0 z * z 1)
  have hpos_on : ∀ y ∈ Metric.ball ctr 1, 0 < biotSavartKernel 0 y * y 1 := by
    intro y hy
    have hy0 := ne_zero_of_mem_closedBall (Metric.ball_subset_closedBall hy)
    rw [biotSavartKernel_of_ne (Ne.symm hy0)]
    have h1 := one_lt_coord_of_mem_ball hy
    have : 0 < ‖(0 : T3) - y‖ := by rw [zero_sub, norm_neg]; exact norm_pos_iff.mpr hy0
    have := Real.rpow_pos_of_pos this (-(3 : ℝ))
    have := Real.pi_pos
    positivity
  have hg0 : 0 ≤ g := by
    intro y
    simp only [g, Pi.zero_apply]
    by_cases hy : y ∈ Metric.ball ctr 1
    · rw [Set.indicator_of_mem hy]; exact (hpos_on y hy).le
    · rw [Set.indicator_of_notMem hy]
  have hgi : Integrable g NavierStokes3D.volume := by
    have := hint.neg
    refine (hint.norm.mono' ?_ ?_)
    · -- measurability of g from the integrable vector field via the coordinate identity
      have hm := ((EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.comp_aestronglyMeasurable
        hint.aestronglyMeasurable).neg
      refine hm.congr (Filter.Eventually.of_forall fun y => ?_)
      show -(EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)) _ = g y
      rw [hp, bsField0_coord2, neg_neg]
    · refine Filter.Eventually.of_forall fun y => ?_
      have := PiLp.norm_apply_le
        (biotSavartKernel 0 y • cross (indField (Metric.ball ctr 1) e1 y) (0 - y)) 2
      rw [bsField0_coord2, norm_neg] at this
      exact this
  have hpos : 0 < ∫ y, g y ∂NavierStokes3D.volume := by
    rw [integral_pos_iff_support_of_nonneg hg0 hgi]
    have hsub : Metric.ball ctr 1 ⊆ Function.support g := by
      intro y hy
      simp only [Function.mem_support, g, Set.indicator_of_mem hy]
      exact (hpos_on y hy).ne'
    exact lt_of_lt_of_le (Metric.measure_ball_pos MeasureTheory.volume ctr one_pos)
      (MeasureTheory.measure_mono hsub)
  exact hpos.ne' hcomm

/-- **Refutation of the former hypothesis `KineticEnergyDerivIsVelocity`.**
With the repository's definitions (`FunctionalDerivative` = the unique `L²` functional gradient
on regular vorticities, else `0`; `velocity_from_vorticity` = the ℝ³ Biot–Savart integral), the
statement `∀ ω, FunctionalDerivative KineticEnergyHamiltonian ω = velocity_from_vorticity ω` is
FALSE. Counterexample: `ω = 1_B e₁` with `B` the unit ball at `(0,2,0)`; it is in
`CoadjointOrbit` (its `fderiv`-based `div` vanishes identically) and is not differentiable, so its
functional derivative is `0`, while its Biot–Savart velocity is nonzero at the origin. This is a
statement about a rough field; the smooth-field identity is not decided here. -/
theorem not_forall_functionalDerivative_kineticEnergy_eq_velocity :
    ¬ ∀ ω : CoadjointOrbit,
      FunctionalDerivative KineticEnergyHamiltonian ω = velocity_from_vorticity ω := by
  intro H
  let B := Metric.ball ctr 1
  have hnd : ¬ ∀ i x, DifferentiableAt ℝ (fun y => (indOrbit B ((1 : ℝ) • e1)).val y i) x := by
    intro hall
    apply not_differentiableAt_indField ((1 : ℝ) • e1) (by simp [e1])
    exact hall 0 (ctr + e1)
  have h1 := H (indOrbit B ((1 : ℝ) • e1))
  rw [functionalDerivative_of_not_differentiable _ _ hnd, velocity_from_vorticity_eq_BiotSavart]
    at h1
  simp only [indOrbit, one_smul] at h1
  exact biotSavart_indField_ne_zero (congrFun h1 0).symm

/-- Gâteaux representatives are never unique: changing a representative at the single point `0`
gives another one (the pairing integral only sees the a.e. class). -/
theorem not_unique_isGateauxRepresentative (F : CoadjointOrbit → ℝ) (ω : CoadjointOrbit)
    (d : T3 → EuclideanSpace ℝ (Fin 3)) (hd : IsGateauxRepresentative F ω d) :
    ∃ d', IsGateauxRepresentative F ω d' ∧ d' ≠ d := by
  refine ⟨fun x => d x + ({0} : Set T3).indicator (fun _ => e1) x, ?_, ?_⟩
  · rw [isGateauxRepresentative_iff] at hd ⊢
    intro ε hω hε
    have h := hd ε hω hε
    have hae : (fun x => pairing (d x + ({0} : Set T3).indicator (fun _ => e1) x) (ε.val x))
        =ᵐ[NavierStokes3D.volume] fun x => pairing (d x) (ε.val x) := by
      have hnull : NavierStokes3D.volume ({0} : Set T3) = 0 :=
        measure_singleton (μ := (MeasureTheory.volume : Measure T3)) 0
      have : ∀ᵐ x ∂NavierStokes3D.volume, x ∉ ({0} : Set T3) :=
        measure_eq_zero_iff_ae_notMem.mp hnull
      filter_upwards [this] with x hx
      rw [Set.indicator_of_notMem hx, add_zero]
    rw [integral_congr_ae hae]
    exact h
  · intro h
    have := congrFun h 0
    rw [Set.indicator_of_mem (Set.mem_singleton 0), add_eq_left] at this
    have h0 : e1 0 = 0 := by rw [this]; rfl
    simp [e1] at h0

/-- Consequently the hypotheses of `functional_derivative_eq_velocity_of_unique_repr`
("`u` is a representative and the only one") can never hold together. -/
theorem not_unique_velocity_representative (ω : CoadjointOrbit) :
    ¬ (IsGateauxRepresentative KineticEnergyHamiltonian ω (velocity_from_vorticity ω) ∧
      ∀ dH, IsGateauxRepresentative KineticEnergyHamiltonian ω dH →
        dH = velocity_from_vorticity ω) := by
  rintro ⟨h, huniq⟩
  obtain ⟨d', hd', hne⟩ := not_unique_isGateauxRepresentative _ ω _ h
  exact hne (huniq d' hd')

end KineticEnergyDerivative

end
