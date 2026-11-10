/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import FrohmanianTether.TestFieldFamily
public import FrohmanianTether.TetherWeight
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# The corrected weight hypothesis holds for the tether

`tetherKernel_aeEnstrophyWeight : AEEnstrophyWeight TetherKernel` — every density `α` of
`TetherKernel` that is locally integrable at regular vorticities equals `-κ ‖ω‖²` almost
everywhere at every regular `ω`.

Proof outline (all steps proved here):

* `projCoef ω v` is the Gram–Schmidt coefficient of `Π_u`; on test fields it is additive
  (`projCoef_add_smul`), because either `∫ ‖u‖² = 0` (then it is `0`) or `u ∈ L²`.
* For test fields `a, b` with `projCoef ω a = projCoef ω b = 0`, `Π_u a = a`, `Π_u b = b`
  a.e., and the density equation for the linear functionals `linFun a`, `linFun b` gives
  `∫ β ⟨a, b⟩ = 0` with `β = α ω + κ ‖ω‖²` (`integral_beta_eq_zero`). All products are
  integrable (`α ω` locally integrable, `⟨a, b⟩` continuous with compact support).
* A point `x` is *good* if `∫ β ⟨a, b⟩ = 0` for all test fields supported in some ball
  `B(x, ε)`. Points where `projCoef` vanishes on all small test fields are good; if two other
  points have test fields with nonzero coefficient arbitrarily close to them, those serve as
  correctors that make `a, b` orthogonal to `u` without changing `⟨a, b⟩` pointwise
  (`good_of_two_correctors`). Hence at most two points are not good (`bad_finite`).
* On a good ball, `β` integrates to `0` against every smooth compactly supported `g`: with a
  bump `χ ≡ 1` near `supp g`, `g = ⟨curl(x₀ g e₂), curl(x₀ χ e₂)⟩ - ⟨curl(g e₂), curl(x₀²/2 χ e₂)⟩`
  pointwise (`pointwise_identity`). Mathlib's
  `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` then gives `β = 0` a.e. on the ball.
* A countable subcover of the good set and the finite bad set give `β = 0` a.e.
-/

open MeasureTheory NavierStokes3D ArnoldGeometric ForMathlib FrohmanianTether TetherNondegeneracy
  TestFieldFamily
open scoped InnerProductSpace

noncomputable section

namespace TetherWeightProof

/-- The Gram–Schmidt coefficient of `Π_u`, `u` the Biot–Savart velocity of `ω`. -/
@[expose] public def projCoef (ω : CoadjointOrbit) (v : T3 → EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (∫ y, pairing (v y) (velocity_from_vorticity ω y) ∂NavierStokes3D.volume) /
    (∫ y, ‖velocity_from_vorticity ω y‖ ^ 2 ∂NavierStokes3D.volume)

public theorem pi_u_eq (ω : CoadjointOrbit) (v : T3 → EuclideanSpace ℝ (Fin 3)) (x : T3) :
    Pi_u (velocity_from_vorticity ω) v x = v x - projCoef ω v • velocity_from_vorticity ω x := rfl

public theorem projCoef_congr_ae (ω : CoadjointOrbit) {v w : T3 → EuclideanSpace ℝ (Fin 3)}
    (h : v =ᵐ[MeasureTheory.volume] w) : projCoef ω v = projCoef ω w := by
  unfold projCoef
  congr 1
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

/-- On the `L²` class of a test field with zero coefficient, `Π_u` is the identity a.e. -/
public theorem pi_u_testToL2_ae (ω : CoadjointOrbit) {a : CoadjointOrbit} (ha : IsTestDirection a)
    (h0 : projCoef ω a.val = 0) :
    Pi_u (velocity_from_vorticity ω) ⇑(testToL2 a ha) =ᵐ[MeasureTheory.volume] a.val := by
  have hae : ⇑(testToL2 a ha) =ᵐ[MeasureTheory.volume] a.val := ha.memLp.coeFn_toLp
  have hc : projCoef ω ⇑(testToL2 a ha) = 0 := by rw [projCoef_congr_ae ω hae, h0]
  filter_upwards [hae] with x hx
  rw [pi_u_eq, hc, zero_smul, sub_zero, hx]

public theorem hasCompactSupport_inner {a b : CoadjointOrbit} (ha : IsTestDirection a) :
    HasCompactSupport (fun x => inner ℝ (a.val x) (b.val x)) :=
  ha.2.mono' (fun x hx => subset_tsupport _ (fun h => hx (by simp [h])))

public theorem continuous_inner_test {a b : CoadjointOrbit} (ha : IsTestDirection a)
    (hb : IsTestDirection b) : Continuous (fun x => inner ℝ (a.val x) (b.val x)) :=
  ha.1.continuous.inner hb.1.continuous

public theorem integrable_mul_inner {β : T3 → ℝ}
    (hβ : LocallyIntegrable β (MeasureTheory.volume : Measure T3))
    {a b : CoadjointOrbit} (ha : IsTestDirection a) (hb : IsTestDirection b) :
    Integrable (fun x => β x * inner ℝ (a.val x) (b.val x)) MeasureTheory.volume := by
  simpa [smul_eq_mul] using hβ.integrable_smul_right_of_hasCompactSupport
    (continuous_inner_test ha hb) (hasCompactSupport_inner (b := b) ha)

/-- The density equation tested on two test fields orthogonal to `u`. -/
public theorem integral_beta_eq_zero {α : CoadjointOrbit → T3 → ℝ}
    (hα : HasTetherKernelDensity TetherKernel α) {ω : CoadjointOrbit} (hω : IsRegularVorticity ω)
    (hloc : LocallyIntegrable (α ω) (MeasureTheory.volume : Measure T3))
    {a b : CoadjointOrbit} (ha : IsTestDirection a) (hb : IsTestDirection b)
    (ha0 : projCoef ω a.val = 0) (hb0 : projCoef ω b.val = 0) :
    ∫ x, (α ω x + kappa * Enstrophy ω) * inner ℝ (a.val x) (b.val x) ∂MeasureTheory.volume = 0 := by
  have e := hα ω (linFun a) (linFun b)
  rw [tetherKernel_eq, functionalDerivative_eq (linFun_gradient hω a ha),
    functionalDerivative_eq (linFun_gradient hω b hb)] at e
  have hA := pi_u_testToL2_ae ω ha ha0
  have hB := pi_u_testToL2_ae ω hb hb0
  have e1 : tI ω ⇑(testToL2 a ha) ⇑(testToL2 b hb) = ∫ x, inner ℝ (a.val x) (b.val x) := by
    unfold tI
    apply integral_congr_ae
    filter_upwards [hA, hB] with x h1 h2
    rw [h1, h2]
  have e2 : (∫ x, α ω x * inner ℝ (Pi_u (velocity_from_vorticity ω) ⇑(testToL2 a ha) x)
      (Pi_u (velocity_from_vorticity ω) ⇑(testToL2 b hb) x) ∂NavierStokes3D.volume) =
      ∫ x, α ω x * inner ℝ (a.val x) (b.val x) := by
    apply integral_congr_ae
    filter_upwards [hA, hB] with x h1 h2
    rw [h1, h2]
  rw [e1, e2] at e
  have hI1 := integrable_mul_inner hloc ha hb
  have hI2 : Integrable (fun x => kappa * Enstrophy ω * inner ℝ (a.val x) (b.val x))
      MeasureTheory.volume :=
    ((continuous_inner_test ha hb).integrable_of_hasCompactSupport
      (hasCompactSupport_inner (b := b) ha)).const_mul _
  simp_rw [add_mul]
  rw [integral_add hI1 (by simpa [mul_assoc] using hI2), ← e]
  simp_rw [mul_assoc]
  simp only [integral_const_mul]
  ring

/-- The coefficient is additive along test fields at a regular vorticity. -/
public theorem projCoef_add_smul {ω : CoadjointOrbit} (hω : IsRegularVorticity ω)
    {a c : CoadjointOrbit} (ha : IsTestDirection a) (hc : IsTestDirection c) (t : ℝ) :
    projCoef ω (fun x => a.val x + t • c.val x) = projCoef ω a.val + t * projCoef ω c.val := by
  set u := velocity_from_vorticity ω
  by_cases hE : (∫ y, ‖u y‖ ^ 2 ∂NavierStokes3D.volume) = 0
  · simp [projCoef, u, hE]
  have hu2 : Integrable (fun y => ‖u y‖ ^ 2) MeasureTheory.volume := by
    by_contra h; exact hE (integral_undef h)
  have hum : AEStronglyMeasurable u MeasureTheory.volume := by
    simp only [u, velocity_from_vorticity_eq_BiotSavart]
    exact (stronglyMeasurable_biotSavart hω.continuous).aestronglyMeasurable
  have hint : ∀ {e : CoadjointOrbit}, IsTestDirection e →
      Integrable (fun y => pairing (e.val y) (u y)) MeasureTheory.volume := by
    intro e he
    have he2 : Integrable (fun y => ‖e.val y‖ ^ 2) MeasureTheory.volume :=
      (he.1.continuous.norm.pow 2).integrable_of_hasCompactSupport
        (he.2.mono' (fun x hx => subset_tsupport _ (fun h => hx (by simp [h]))))
    refine Integrable.mono' (he2.add hu2) (he.1.continuous.aestronglyMeasurable.inner hum) ?_
    refine Filter.Eventually.of_forall fun y => ?_
    simp only [pairing, Real.norm_eq_abs, Pi.add_apply]
    have h1 := abs_real_inner_le_norm (e.val y) (u y)
    nlinarith [sq_nonneg (‖e.val y‖ - ‖u y‖), norm_nonneg (e.val y), norm_nonneg (u y)]
  unfold projCoef
  have hnum : (∫ y, pairing (a.val y + t • c.val y) (u y) ∂NavierStokes3D.volume) =
      (∫ y, pairing (a.val y) (u y) ∂NavierStokes3D.volume) +
        t * ∫ y, pairing (c.val y) (u y) ∂NavierStokes3D.volume := by
    simp only [pairing, inner_add_left, inner_smul_left, RCLike.conj_to_real,
      show (NavierStokes3D.volume : Measure T3) = MeasureTheory.volume from rfl]
    have h1 := hint ha
    have h2 := (hint hc).const_mul t
    simp only [pairing] at h1 h2
    rw [integral_add h1 h2, integral_const_mul]
  rw [hnum, add_div, mul_div_assoc]

/-- The test field `a + t c`. -/
@[expose] public def comb (a c : CoadjointOrbit) (ha : IsTestDirection a) (hc : IsTestDirection c)
    (t : ℝ) : CoadjointOrbit :=
  orbitLine a c ha.regular hc.regular t

public theorem comb_val (a c : CoadjointOrbit) (ha : IsTestDirection a) (hc : IsTestDirection c)
    (t : ℝ) : (comb a c ha hc t).val = fun x => a.val x + t • c.val x := rfl

public theorem comb_test {a c : CoadjointOrbit} (ha : IsTestDirection a) (hc : IsTestDirection c)
    (t : ℝ) : IsTestDirection (comb a c ha hc t) := by
  refine ⟨ha.1.add (hc.1.const_smul t), ?_⟩
  rw [comb_val]
  exact ha.2.add (hc.2.smul_left (f := fun _ => t))

/-! ### Good points, correctors and the bad set (abstract `β`, coefficient `lam`) -/

section Abstract

/-- `∫ β ⟨a, b⟩ = 0`. -/
@[expose] public def Kills (β : T3 → ℝ) (a b : CoadjointOrbit) : Prop :=
  ∫ x, β x * inner ℝ (a.val x) (b.val x) ∂MeasureTheory.volume = 0

/-- `x` is good: `β` is killed by all pairs of test fields supported in some ball `B(x, ε)`. -/
@[expose] public def GoodPt (β : T3 → ℝ) (x : T3) : Prop :=
  ∃ ε > 0, ∀ a b : CoadjointOrbit, IsTestDirection a → IsTestDirection b →
    tsupport a.val ⊆ Metric.ball x ε → tsupport b.val ⊆ Metric.ball x ε → Kills β a b

/-- Test fields with nonzero coefficient exist arbitrarily close to `x`. -/
@[expose] public def CoefPt (lam : (T3 → EuclideanSpace ℝ (Fin 3)) → ℝ) (x : T3) : Prop :=
  ∀ ε > 0, ∃ c : CoadjointOrbit, IsTestDirection c ∧ tsupport c.val ⊆ Metric.ball x ε ∧
    lam c.val ≠ 0

/-- Hypothesis shape: `β` is killed by test pairs with zero coefficient. -/
@[expose] public def KillsOrth (β : T3 → ℝ) (lam : (T3 → EuclideanSpace ℝ (Fin 3)) → ℝ) : Prop :=
  ∀ a b : CoadjointOrbit, IsTestDirection a → IsTestDirection b → lam a.val = 0 →
    lam b.val = 0 → Kills β a b

/-- Hypothesis shape: the coefficient is additive along test fields. -/
@[expose] public def CoefAdditive (lam : (T3 → EuclideanSpace ℝ (Fin 3)) → ℝ) : Prop :=
  ∀ a c : CoadjointOrbit, IsTestDirection a → IsTestDirection c → ∀ t : ℝ,
    lam (fun x => a.val x + t • c.val x) = lam a.val + t * lam c.val

public theorem good_of_not_coefPt {β : T3 → ℝ} {lam : (T3 → EuclideanSpace ℝ (Fin 3)) → ℝ}
    (HV : KillsOrth β lam) {x : T3} (hx : ¬ CoefPt lam x) : GoodPt β x := by
  unfold CoefPt at hx
  push Not at hx
  obtain ⟨ε, hε, h⟩ := hx
  exact ⟨ε, hε, fun a b ha hb hsa hsb => HV a b ha hb (h a ha hsa) (h b hb hsb)⟩

theorem zero_or_zero {f g : T3 → EuclideanSpace ℝ (Fin 3)} {s t : Set T3} (hf : tsupport f ⊆ s)
    (hg : tsupport g ⊆ t) (hd : Disjoint s t) (z : T3) : f z = 0 ∨ g z = 0 := by
  by_cases hz : z ∈ s
  · right
    exact image_eq_zero_of_notMem_tsupport fun h => Set.disjoint_left.1 hd hz (hg h)
  · left
    exact image_eq_zero_of_notMem_tsupport fun h => hz (hf h)

/-- **Correctors.** Two points other than `x` near which test fields with nonzero coefficient
exist make `x` good: subtracting multiples of those fields makes `a, b` orthogonal to `u`
without changing `⟨a, b⟩` pointwise. -/
public theorem good_of_two_correctors {β : T3 → ℝ} {lam : (T3 → EuclideanSpace ℝ (Fin 3)) → ℝ}
    (HV : KillsOrth β lam) (Hlin : CoefAdditive lam) {x y w : T3} (hxy : x ≠ y) (hxw : x ≠ w)
    (hyw : y ≠ w) (hy : CoefPt lam y) (hw : CoefPt lam w) : GoodPt β x := by
  set r0 := min (dist x y) (min (dist x w) (dist y w)) / 2 with hr0
  have hpos : 0 < r0 := by
    have := dist_pos.2 hxy; have := dist_pos.2 hxw; have := dist_pos.2 hyw
    positivity
  have d1 : r0 + r0 ≤ dist x w := by
    have := min_le_right (dist x y) (min (dist x w) (dist y w))
    have := min_le_left (dist x w) (dist y w); linarith
  have d2 : r0 + r0 ≤ dist y x := by
    rw [dist_comm]; have := min_le_left (dist x y) (min (dist x w) (dist y w)); linarith
  have d3 : r0 + r0 ≤ dist y w := by
    have := min_le_right (dist x y) (min (dist x w) (dist y w))
    have := min_le_right (dist x w) (dist y w); linarith
  obtain ⟨c, hc, hcs, hc0⟩ := hy r0 hpos
  obtain ⟨d, hd, hds, hd0⟩ := hw r0 hpos
  refine ⟨r0, hpos, fun a b ha hb hsa hsb => ?_⟩
  set s := -lam a.val / lam c.val
  set t := -lam b.val / lam d.val
  have ha' : lam (comb a c ha hc s).val = 0 := by
    rw [comb_val, Hlin a c ha hc s]; simp only [s]; field_simp; ring
  have hb' : lam (comb b d hb hd t).val = 0 := by
    rw [comb_val, Hlin b d hb hd t]; simp only [t]; field_simp; ring
  have h := HV _ _ (comb_test ha hc s) (comb_test hb hd t) ha' hb'
  have z1 := zero_or_zero hsa hds (Metric.ball_disjoint_ball d1)
  have z2 := zero_or_zero hcs hsb (Metric.ball_disjoint_ball d2)
  have z3 := zero_or_zero hcs hds (Metric.ball_disjoint_ball d3)
  have hpt : ∀ z, inner ℝ (a.val z + s • c.val z) (b.val z + t • d.val z) =
      inner ℝ (a.val z) (b.val z) := by
    intro z
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real]
    have e1 : inner ℝ (a.val z) (d.val z) = 0 := by rcases z1 z with h | h <;> simp [h]
    have e2 : inner ℝ (c.val z) (b.val z) = 0 := by rcases z2 z with h | h <;> simp [h]
    have e3 : inner ℝ (c.val z) (d.val z) = 0 := by rcases z3 z with h | h <;> simp [h]
    rw [e1, e2, e3]; ring
  unfold Kills at h ⊢
  simpa only [comb_val, hpt] using h

/-- At most two points are not good. -/
public theorem bad_finite {β : T3 → ℝ} {lam : (T3 → EuclideanSpace ℝ (Fin 3)) → ℝ}
    (HV : KillsOrth β lam) (Hlin : CoefAdditive lam) : {x | ¬ GoodPt β x}.Finite := by
  have hcoef : ∀ x, ¬ GoodPt β x → CoefPt lam x := fun x hx => by
    by_contra h; exact hx (good_of_not_coefPt HV h)
  by_cases h : ∃ x y, ¬ GoodPt β x ∧ ¬ GoodPt β y ∧ x ≠ y
  · obtain ⟨x, y, hx, hy, hxy⟩ := h
    apply (Set.toFinite ({x, y} : Set T3)).subset
    intro w hw
    by_contra hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
    exact hw (good_of_two_correctors HV Hlin hne.1 hne.2 hxy (hcoef x hx) (hcoef y hy))
  · push Not at h
    exact Set.Subsingleton.finite fun x hx y hy => h x y hx hy

end Abstract

/-! ### The local fundamental lemma on a good ball -/

theorem hasFDerivAt_coord (z : T3) :
    HasFDerivAt (fun y : T3 => y 0) (EuclideanSpace.proj (0 : Fin 3) : T3 →L[ℝ] ℝ) z :=
  (EuclideanSpace.proj (0 : Fin 3) : T3 →L[ℝ] ℝ).hasFDerivAt

theorem proj_eb (i : Fin 3) :
    (EuclideanSpace.proj (0 : Fin 3) : T3 →L[ℝ] ℝ) (eb i) = if i = 0 then 1 else 0 := by
  fin_cases i <;> simp [eb]

/-- The pointwise identity `g = ⟨curl(x₀ g e₂), curl(x₀ χ e₂)⟩ - ⟨curl(g e₂), curl(x₀²/2 χ e₂)⟩`
when `χ = 1` near `supp g`. -/
public theorem pointwise_identity {g χ : T3 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hχ : ∀ z ∈ tsupport g, χ =ᶠ[nhds z] fun _ => 1) (z : T3) :
    pd (fun y => y 0 * g y) 0 z * pd (fun y => y 0 * χ y) 0 z +
        pd (fun y => y 0 * g y) 1 z * pd (fun y => y 0 * χ y) 1 z -
      (pd g 0 z * pd (fun y => y 0 * y 0 / 2 * χ y) 0 z +
        pd g 1 z * pd (fun y => y 0 * y 0 / 2 * χ y) 1 z) = g z := by
  have hgd : HasFDerivAt g (fderiv ℝ g z) z :=
    ((hg.differentiable (by norm_cast)) z).hasFDerivAt
  have hH1 : HasFDerivAt (fun y => y 0 * g y)
      (z 0 • fderiv ℝ g z + g z • (EuclideanSpace.proj (0 : Fin 3) : T3 →L[ℝ] ℝ)) z :=
    (hasFDerivAt_coord z).mul hgd
  by_cases hz : z ∈ tsupport g
  · have hev := hχ z hz
    have hK1 : (fun y : T3 => y 0 * χ y) =ᶠ[nhds z] fun y => y 0 := by
      filter_upwards [hev] with y hy; rw [hy, mul_one]
    have hK2 : (fun y : T3 => y 0 * y 0 / 2 * χ y) =ᶠ[nhds z] fun y => y 0 * y 0 / 2 := by
      filter_upwards [hev] with y hy; rw [hy, mul_one]
    have hX2 : HasFDerivAt (fun y : T3 => y 0 * y 0 / 2)
        ((2:ℝ)⁻¹ • (z 0 • (EuclideanSpace.proj (0 : Fin 3) : T3 →L[ℝ] ℝ) +
          z 0 • (EuclideanSpace.proj (0 : Fin 3) : T3 →L[ℝ] ℝ))) z := by
      have := ((hasFDerivAt_coord z).mul (hasFDerivAt_coord z)).const_mul (2:ℝ)⁻¹
      convert this using 1
      funext y; simp only [Pi.mul_apply]; ring
    simp only [pd, hK1.fderiv_eq, hK2.fderiv_eq, (hasFDerivAt_coord z).fderiv, hX2.fderiv,
      hH1.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, proj_eb, smul_eq_mul]
    simp
    ring
  · have hg0 : g =ᶠ[nhds z] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.1 hz
    have hH0 : (fun y : T3 => y 0 * g y) =ᶠ[nhds z] fun _ => 0 := by
      filter_upwards [hg0] with y hy; rw [hy, mul_zero]
    have hgz : g z = 0 := image_eq_zero_of_notMem_tsupport hz
    simp only [pd, hg0.fderiv_eq, hH0.fderiv_eq, fderiv_const_apply, hgz]
    simp

/-- **Local fundamental lemma.** On a good ball, `β` vanishes almost everywhere. -/
public theorem ae_zero_on_good_ball {β : T3 → ℝ}
    (hβ : LocallyIntegrable β (MeasureTheory.volume : Measure T3)) {x : T3} {ε : ℝ} (hε : 0 < ε)
    (hgood : ∀ a b : CoadjointOrbit, IsTestDirection a → IsTestDirection b →
      tsupport a.val ⊆ Metric.ball x ε → tsupport b.val ⊆ Metric.ball x ε → Kills β a b) :
    ∀ᵐ z ∂(MeasureTheory.volume : Measure T3), z ∈ Metric.ball x ε → β z = 0 := by
  refine Metric.isOpen_ball.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hβ.locallyIntegrableOn _) ?_
  intro g hg hgc hgs
  obtain ⟨r', hr'ε, hgr'⟩ := exists_lt_subset_ball (isClosed_tsupport g) hgs
  set ρ := max r' (ε / 2) with hρ
  have hρpos : 0 < ρ := lt_max_of_lt_right (by linarith)
  have hρε : ρ < ε := max_lt hr'ε (by linarith)
  let χ : ContDiffBump x := ⟨ρ, (ρ + ε) / 2, hρpos, by linarith⟩
  have hχ1 : ∀ z ∈ tsupport g, (χ : T3 → ℝ) =ᶠ[nhds z] fun _ => 1 := by
    intro z hz
    have hzb : z ∈ Metric.ball x ρ :=
      Metric.ball_subset_ball (le_max_left _ _) (hgr' hz)
    filter_upwards [Metric.isOpen_ball.mem_nhds hzb] with y hy
    exact χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
  have hχs : tsupport (χ : T3 → ℝ) ⊆ Metric.ball x ε := by
    rw [χ.tsupport_eq]
    exact Metric.closedBall_subset_ball (by simp only [χ]; linarith)
  have hX : ContDiff ℝ (⊤ : ℕ∞) (fun y : T3 => y 0) :=
    (EuclideanSpace.proj (0 : Fin 3) : T3 →L[ℝ] ℝ).contDiff
  have hg' : ContDiff ℝ (⊤ : ℕ∞) g := hg.of_le (by exact_mod_cast le_top)
  have hχd : ContDiff ℝ (⊤ : ℕ∞) (χ : T3 → ℝ) := χ.contDiff
  set H1 : T3 → ℝ := fun y => y 0 * g y
  set K1 : T3 → ℝ := fun y => y 0 * χ y
  set K2 : T3 → ℝ := fun y => y 0 * y 0 / 2 * χ y
  have cH1 : ContDiff ℝ (⊤ : ℕ∞) H1 := hX.mul hg'
  have cK1 : ContDiff ℝ (⊤ : ℕ∞) K1 := hX.mul hχd
  have cK2 : ContDiff ℝ (⊤ : ℕ∞) K2 := ((hX.mul hX).div_const 2).mul hχd
  have sH1 : HasCompactSupport H1 := hgc.mul_left
  have sK1 : HasCompactSupport K1 := χ.hasCompactSupport.mul_left
  have sK2 : HasCompactSupport K2 := χ.hasCompactSupport.mul_left
  have tH1 : tsupport H1 ⊆ Metric.ball x ε := (tsupport_mul_subset_right).trans hgs
  have tK1 : tsupport K1 ⊆ Metric.ball x ε := (tsupport_mul_subset_right).trans hχs
  have tK2 : tsupport K2 ⊆ Metric.ball x ε := (tsupport_mul_subset_right).trans hχs
  have k1 := hgood (curlOrbit H1 cH1) (curlOrbit K1 cK1) (curlOrbit_test cH1 sH1)
    (curlOrbit_test cK1 sK1) ((tsupport_curlVal_subset H1).trans tH1)
    ((tsupport_curlVal_subset K1).trans tK1)
  have k2 := hgood (curlOrbit g hg') (curlOrbit K2 cK2) (curlOrbit_test hg' hgc)
    (curlOrbit_test cK2 sK2) ((tsupport_curlVal_subset g).trans hgs)
    ((tsupport_curlVal_subset K2).trans tK2)
  have I1 := integrable_mul_inner hβ (curlOrbit_test cH1 sH1) (curlOrbit_test cK1 sK1)
  have I2 := integrable_mul_inner hβ (curlOrbit_test hg' hgc) (curlOrbit_test cK2 sK2)
  unfold Kills at k1 k2
  have hpt : ∀ z, g z • β z = β z * inner ℝ ((curlOrbit H1 cH1).val z) ((curlOrbit K1 cK1).val z) -
      β z * inner ℝ ((curlOrbit g hg').val z) ((curlOrbit K2 cK2).val z) := by
    intro z
    simp only [curlOrbit_val, inner_curlVal, smul_eq_mul]
    rw [← pointwise_identity hg' hχ1 z]
    ring
  simp_rw [hpt]
  rw [integral_sub I1 I2, k1, k2, sub_zero]

/-- **Global step.** A locally integrable `β` killed by all test pairs orthogonal to `u`
(for an additive coefficient) vanishes almost everywhere. -/
public theorem ae_zero_of_killsOrth {β : T3 → ℝ} {lam : (T3 → EuclideanSpace ℝ (Fin 3)) → ℝ}
    (hβ : LocallyIntegrable β (MeasureTheory.volume : Measure T3)) (HV : KillsOrth β lam)
    (Hlin : CoefAdditive lam) : ∀ᵐ z ∂(MeasureTheory.volume : Measure T3), β z = 0 := by
  set N := {x | ¬ GoodPt β x}
  have hN0 : (MeasureTheory.volume : Measure T3) N = 0 := (bad_finite HV Hlin).measure_zero _
  let ι := {x // GoodPt β x}
  choose ε hε hgood using fun i : ι => i.2
  let s : ι → Set T3 := fun i => Metric.ball i.1 (ε i)
  obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable s (fun i => Metric.isOpen_ball)
  have hloc : ∀ i, ∀ᵐ z ∂(MeasureTheory.volume : Measure T3), z ∈ s i → β z = 0 :=
    fun i => ae_zero_on_good_ball hβ (hε i) (hgood i)
  rw [ae_iff]
  refine measure_mono_null (t := N ∪ ⋃ i ∈ T, {z | ¬ (z ∈ s i → β z = 0)}) ?_
    (measure_union_null hN0 ((measure_biUnion_null_iff hT).2 fun i _ => ae_iff.1 (hloc i)))
  intro z hz
  by_cases hzN : z ∈ N
  · exact Or.inl hzN
  · right
    have hzg : GoodPt β z := by simpa [N] using hzN
    have hzU : z ∈ ⋃ i, s i := Set.mem_iUnion.2 ⟨⟨z, hzg⟩, Metric.mem_ball_self (hε _)⟩
    rw [← hTU] at hzU
    obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.1 hzU
    exact Set.mem_iUnion₂.2 ⟨i, hi, fun h => hz (h hzi)⟩

/-- **The corrected weight hypothesis holds for the tether** (with `c = κ`). -/
public theorem tetherKernel_aeEnstrophyWeight : AEEnstrophyWeight TetherKernel := by
  intro α hα hloc
  refine ⟨kappa, fun ω hω => ?_⟩
  set β : T3 → ℝ := fun x => α ω x + kappa * Enstrophy ω
  have hβ : LocallyIntegrable β (MeasureTheory.volume : Measure T3) :=
    (hloc ω hω).add (locallyIntegrable_const _)
  have HV : KillsOrth β (projCoef ω) := fun a b ha hb ha0 hb0 =>
    integral_beta_eq_zero hα hω (hloc ω hω) ha hb ha0 hb0
  have Hlin : CoefAdditive (projCoef ω) := fun a c ha hc t => projCoef_add_smul hω ha hc t
  filter_upwards [ae_zero_of_killsOrth hβ HV Hlin] with x hx
  simp only [β] at hx
  linarith

/-- Sanity: the hypotheses of the weight condition are satisfiable (the canonical density is a
locally integrable density of the tether), and its conclusion is not vacuous: at the regular
vorticity `rotOrbit 0` the enstrophy is positive, so the weight `-κ ‖ω‖²` is nonzero. -/
public theorem aeEnstrophyWeight_nontrivial :
    HasTetherKernelDensity TetherKernel canonicalTetherDensity ∧
    (∀ ω, IsRegularVorticity ω →
      LocallyIntegrable (canonicalTetherDensity ω) (MeasureTheory.volume : Measure T3)) ∧
    IsRegularVorticity (rotOrbit 0) ∧ -kappa * Enstrophy (rotOrbit 0) ≠ 0 := by
  refine ⟨tetherKernel_has_canonical_density, fun ω _ => canonicalTetherDensity_locallyIntegrable ω,
    (rot_test 0).regular, ?_⟩
  have hE : 0 < Enstrophy (rotOrbit 0) := by
    simpa [Enstrophy, Casimir, rotOrbit] using integral_rotField_pos 0
  have hk : kappa ≠ 0 := by rw [kappa_eq_three_halves]; norm_num
  exact mul_ne_zero (neg_ne_zero.mpr hk) hE.ne'

/-- The density and weight inputs of `uniqueness_of_minimal_tether_core` hold for `B = TetherKernel`
(the weight input is discharged by `tetherKernel_aeEnstrophyWeight`). -/
public theorem tetherKernel_core_inputs :
    (∃ α, HasTetherKernelDensity TetherKernel α ∧
      ∀ ω, IsRegularVorticity ω → LocallyIntegrable (α ω) (MeasureTheory.volume : Measure T3)) ∧
    AEEnstrophyWeight TetherKernel ∧ SaturatesTetherQuadratic TetherKernel :=
  ⟨⟨canonicalTetherDensity, tetherKernel_has_canonical_density,
      fun ω _ => canonicalTetherDensity_locallyIntegrable ω⟩,
    tetherKernel_aeEnstrophyWeight, tetherKernel_kernel_conditions.1⟩

end TetherWeightProof

end
