/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import FrohmanianTether.Uniqueness

/-!
# The weight hypothesis for the tether: refutation of the unrestricted form

`AEEnstrophyWeightUnrestricted B` asks that EVERY density `α` of `B` (no measurability
condition) equal `-c ‖ω‖²` almost everywhere at regular vorticities. This module REFUTES it for
`TetherKernel`:

* `vitaliSet` — a Vitali-type set `V ⊆ ball 0 1` in `ℝ³`: one representative in the unit ball of
  each class of `ℝ³ / ℚ e₀` meeting the ball.
* `vitaliSet_null_of_subset` — every null-measurable subset of `V` is null (inner measure `0`).
* `vitaliSet_measure_ne_zero` — `V` itself is not null.
* `integral_indicator_vitaliSet_mul` — `∫ 1_V · f = 0` for every `f : ℝ³ → ℝ`.
* `not_aeEnstrophyWeightUnrestricted_tetherKernel` — at `ω = 0` the tether vanishes
  (`Enstrophy 0 = 0`), so `1_V` is a density there, but `1_V` is not `0` a.e.
* `not_aeEnstrophyWeightUnrestricted_of_eq_tether` — consequently a theorem with hypothesis
  `AEEnstrophyWeightUnrestricted B` and conclusion `B = TetherKernel` is vacuous.

The corrected hypothesis `AEEnstrophyWeight` (in `Uniqueness`) only quantifies over densities
that are locally integrable at regular vorticities; whether `TetherKernel` satisfies it is OPEN.
-/

open MeasureTheory NavierStokes3D ArnoldGeometric ForMathlib FrohmanianTether TetherNondegeneracy
open scoped InnerProductSpace

noncomputable section

namespace TetherWeight

/-- The rational line `ℚ e₀` as an additive subgroup of `ℝ³`. -/
@[expose] public def ratLine : AddSubgroup T3 where
  carrier := {v | ∃ q : ℚ, v = (q : ℝ) • eb 0}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨q, rfl⟩ ⟨q', rfl⟩
    exact ⟨q + q', by push_cast; rw [add_smul]⟩
  neg_mem' := by
    rintro _ ⟨q, rfl⟩
    exact ⟨-q, by push_cast; rw [neg_smul]⟩

/-- Class map of points of the unit ball into `ℝ³ / ℚ e₀`. -/
@[expose] public def ballClass (x : Metric.ball (0 : T3) 1) : T3 ⧸ ratLine :=
  QuotientAddGroup.mk x.val

/-- A Vitali-type set: one chosen representative in the unit ball of every class that meets it. -/
@[expose] public def vitaliSet : Set T3 :=
  Set.range (fun c : Set.range ballClass => (Classical.choose c.2).val)

public theorem vitaliSet_subset_ball : vitaliSet ⊆ Metric.ball (0 : T3) 1 := by
  rintro _ ⟨c, rfl⟩
  exact (Classical.choose c.2).2

public theorem vitaliSet_unique {v w : T3} (hv : v ∈ vitaliSet) (hw : w ∈ vitaliSet)
    (h : (QuotientAddGroup.mk v : T3 ⧸ ratLine) = QuotientAddGroup.mk w) : v = w := by
  obtain ⟨c, rfl⟩ := hv
  obtain ⟨d, rfl⟩ := hw
  have hc := Classical.choose_spec c.2
  have hd := Classical.choose_spec d.2
  have : c = d := Subtype.ext (by rw [← hc, ← hd]; exact h)
  subst this; rfl

public theorem exists_vitaliSet_rep {x : T3} (hx : x ∈ Metric.ball (0 : T3) 1) :
    ∃ v ∈ vitaliSet, (QuotientAddGroup.mk v : T3 ⧸ ratLine) = QuotientAddGroup.mk x := by
  let c : Set.range ballClass := ⟨ballClass ⟨x, hx⟩, ⟨_, rfl⟩⟩
  exact ⟨_, ⟨c, rfl⟩, Classical.choose_spec c.2⟩

/-- The translate `A + q e₀`, written as a preimage. -/
@[expose] public def shift (q : ℚ) (A : Set T3) : Set T3 := (fun x => x + -((q : ℝ) • eb 0)) ⁻¹' A

public theorem measure_shift (q : ℚ) (A : Set T3) :
    (MeasureTheory.volume : Measure T3) (shift q A) = MeasureTheory.volume A :=
  measure_preimage_add_right _ _ _

theorem eb0_ne : eb 0 ≠ (0 : T3) := by
  intro h
  have := congrArg (fun v : T3 => v 0) h
  simp [eb] at this

theorem norm_eb0 : ‖eb 0‖ = 1 := by simp [eb]

public theorem shift_disjoint {A : Set T3} (hA : A ⊆ vitaliSet) {q q' : ℚ} (hq : q ≠ q') :
    Disjoint (shift q A) (shift q' A) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  simp only [shift, Set.mem_preimage] at hx hx'
  have hmk : (QuotientAddGroup.mk (x + -((q : ℝ) • eb 0)) : T3 ⧸ ratLine) =
      QuotientAddGroup.mk (x + -((q' : ℝ) • eb 0)) := by
    rw [QuotientAddGroup.eq]
    exact ⟨q - q', by push_cast; rw [sub_smul]; abel⟩
  have e := vitaliSet_unique (hA hx) (hA hx') hmk
  have e' : (q : ℝ) • eb 0 = (q' : ℝ) • eb 0 := by
    have := congrArg (fun v => x - v) e
    simpa using this
  have e2 : ((q : ℝ) - q') • eb 0 = 0 := by rw [sub_smul, e', sub_self]
  rcases smul_eq_zero.mp e2 with h | h
  · exact hq (by exact_mod_cast sub_eq_zero.mp h)
  · exact eb0_ne h

public theorem shift_subset_ball {A : Set T3} (hA : A ⊆ vitaliSet) {q : ℚ} (hq : |(q : ℝ)| ≤ 1) :
    shift q A ⊆ Metric.ball (0 : T3) 2 := by
  intro x hx
  have h1 := vitaliSet_subset_ball (hA hx)
  simp only [Metric.mem_ball, dist_zero_right] at h1 ⊢
  calc ‖x‖ = ‖(x + -((q : ℝ) • eb 0)) + (q : ℝ) • eb 0‖ := by congr 1; abel
    _ ≤ ‖x + -((q : ℝ) • eb 0)‖ + ‖(q : ℝ) • eb 0‖ := norm_add_le _ _
    _ < 1 + 1 := by
        apply add_lt_add_of_lt_of_le h1
        rw [norm_smul, norm_eb0, mul_one, Real.norm_eq_abs]; exact hq
    _ = 2 := by norm_num

/-- Every measurable subset of the Vitali set is null. -/
public theorem vitaliSet_null_of_measurable {A : Set T3} (hA : A ⊆ vitaliSet) (hm : MeasurableSet A) :
    (MeasureTheory.volume : Measure T3) A = 0 := by
  by_contra h0
  have hfin : (MeasureTheory.volume : Measure T3) (Metric.ball (0 : T3) 2) ≠ ⊤ :=
    measure_ball_lt_top.ne
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt h0 hfin
  let q : ℕ → ℚ := fun k => 1 / ((k : ℚ) + 1)
  have hqinj : Function.Injective q := by
    intro a b hab
    simp only [q, one_div, inv_inj] at hab
    exact_mod_cast add_right_cancel hab
  have hq1 : ∀ k, |((q k : ℚ) : ℝ)| ≤ 1 := by
    intro k
    simp only [q]; push_cast
    rw [abs_of_pos (by positivity)]
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range n)) (fun k => shift (q k) A) := by
    intro a _ b _ hab
    exact shift_disjoint hA (fun h => hab (hqinj h))
  have hunion : (MeasureTheory.volume : Measure T3) (⋃ k ∈ Finset.range n, shift (q k) A) =
      n * MeasureTheory.volume A := by
    rw [measure_biUnion_finset hdisj (fun k _ => hm.preimage (measurable_add_const _))]
    simp [measure_shift]
  have hsub : (⋃ k ∈ Finset.range n, shift (q k) A) ⊆ Metric.ball (0 : T3) 2 :=
    Set.iUnion₂_subset fun k _ => shift_subset_ball hA (hq1 k)
  have := measure_mono (μ := (MeasureTheory.volume : Measure T3)) hsub
  rw [hunion] at this
  exact absurd hn (not_lt.mpr this)

/-- Every null-measurable subset of the Vitali set is null (inner measure `0`). -/
public theorem vitaliSet_null_of_subset {S : Set T3} (hS : S ⊆ vitaliSet)
    (hm : NullMeasurableSet S (MeasureTheory.volume : Measure T3)) :
    (MeasureTheory.volume : Measure T3) S = 0 := by
  obtain ⟨A, hAS, hA, hae⟩ := hm.exists_measurable_subset_ae_eq
  rw [← measure_congr hae]
  exact vitaliSet_null_of_measurable (hAS.trans hS) hA

/-- The Vitali set is not null. -/
public theorem vitaliSet_measure_ne_zero : (MeasureTheory.volume : Measure T3) vitaliSet ≠ 0 := by
  intro h0
  have hcov : Metric.ball (0 : T3) 1 ⊆ ⋃ q : ℚ, shift q vitaliSet := by
    intro x hx
    obtain ⟨v, hv, hmk⟩ := exists_vitaliSet_rep hx
    rw [QuotientAddGroup.eq] at hmk
    obtain ⟨q, hq⟩ := hmk
    refine Set.mem_iUnion.mpr ⟨q, ?_⟩
    simp only [shift, Set.mem_preimage]
    have : x + -((q : ℝ) • eb 0) = v := by rw [← hq]; abel
    rw [this]; exact hv
  have hnull : (MeasureTheory.volume : Measure T3) (⋃ q : ℚ, shift q vitaliSet) = 0 :=
    measure_iUnion_null fun q => by rw [measure_shift]; exact h0
  have := measure_mono_null hcov hnull
  exact (Metric.measure_ball_pos _ (0 : T3) one_pos).ne' this

/-- The product of `1_V` with any real function has Bochner integral `0`: either it is not
integrable (integral `0` by convention) or it is a.e. measurable, its support is then a
null-measurable subset of `V`, hence null. -/
public theorem integral_indicator_vitaliSet_mul (f : T3 → ℝ) :
    ∫ x, vitaliSet.indicator (fun _ => (1 : ℝ)) x * f x ∂(MeasureTheory.volume : Measure T3) = 0 := by
  set k : T3 → ℝ := fun x => vitaliSet.indicator (fun _ => (1 : ℝ)) x * f x
  by_cases hint : Integrable k (MeasureTheory.volume : Measure T3)
  · have hS : NullMeasurableSet (k ⁻¹' {0}ᶜ) (MeasureTheory.volume : Measure T3) :=
      hint.aemeasurable.nullMeasurable (measurableSet_singleton 0).compl
    have hsub : k ⁻¹' {0}ᶜ ⊆ vitaliSet := by
      intro x hx
      by_contra hxV
      apply hx
      simp [k, Set.indicator_of_notMem hxV]
    have h0 := vitaliSet_null_of_subset hsub hS
    apply integral_eq_zero_of_ae
    rw [Filter.EventuallyEq, ae_iff]
    exact measure_mono_null (fun x hx => hx) h0
  · exact integral_undef hint

/-- The zero vorticity. -/
@[expose] public def zeroOrbit : CoadjointOrbit := ⟨fun _ => 0, fun x => by simp [NavierStokes3D.div]⟩

public theorem zeroOrbit_regular : IsRegularVorticity zeroOrbit := fun i x => by
  simp [zeroOrbit]

public theorem enstrophy_zeroOrbit : Enstrophy zeroOrbit = 0 := by
  simp [Enstrophy, Casimir, zeroOrbit]

open Classical in
/-- A density of `TetherKernel`: the indicator of the Vitali set at `ω = 0`, the canonical
density elsewhere. -/
@[expose] public def vitaliDensity (ω : CoadjointOrbit) (x : T3) : ℝ :=
  if ω = zeroOrbit then vitaliSet.indicator (fun _ => (1 : ℝ)) x else canonicalTetherDensity ω x

public theorem vitaliDensity_is_density : HasTetherKernelDensity TetherKernel vitaliDensity := by
  intro ω F G
  by_cases h : ω = zeroOrbit
  · subst h
    have : TetherKernel zeroOrbit F G = 0 := by
      simp [TetherKernel, enstrophy_zeroOrbit]
    rw [this]
    simp only [vitaliDensity, if_true]
    exact (integral_indicator_vitaliSet_mul _).symm
  · rw [tetherKernel_has_canonical_density ω F G]
    simp [vitaliDensity, h]

/-- **Refutation of the unrestricted weight hypothesis for the tether.** -/
public theorem not_aeEnstrophyWeightUnrestricted_tetherKernel :
    ¬ AEEnstrophyWeightUnrestricted TetherKernel := by
  intro hw
  obtain ⟨c, hc⟩ := hw vitaliDensity vitaliDensity_is_density
  have h := hc zeroOrbit zeroOrbit_regular
  simp only [vitaliDensity, if_true, enstrophy_zeroOrbit, mul_zero] at h
  rw [ae_iff] at h
  apply vitaliSet_measure_ne_zero
  convert h using 2
  ext x
  by_cases hx : x ∈ vitaliSet <;> simp [hx]

/-- Any `B` equal to the tether fails the unrestricted weight hypothesis; so a theorem with
hypothesis `AEEnstrophyWeightUnrestricted B` and conclusion `B = TetherKernel` is vacuous. -/
public theorem not_aeEnstrophyWeightUnrestricted_of_eq_tether
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (hB : ∀ ω F G, B ω F G = TetherKernel ω F G) : ¬ AEEnstrophyWeightUnrestricted B := by
  have : B = TetherKernel := funext fun ω => funext fun F => funext fun G => hB ω F G
  subst this
  exact not_aeEnstrophyWeightUnrestricted_tetherKernel

/-- The tether has a locally integrable density (the constant canonical one), so it meets the
corrected `h_density` input of `uniqueness_of_minimal_tether_core`. -/
public theorem tetherKernel_has_locallyIntegrable_density :
    ∃ α, HasTetherKernelDensity TetherKernel α ∧
      ∀ ω, IsRegularVorticity ω → LocallyIntegrable (α ω) (MeasureTheory.volume : Measure T3) :=
  ⟨canonicalTetherDensity, tetherKernel_has_canonical_density,
    fun ω _ => canonicalTetherDensity_locallyIntegrable ω⟩

end TetherWeight

end
