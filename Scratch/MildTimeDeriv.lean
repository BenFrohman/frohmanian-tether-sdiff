import Scratch.DuhamelDeriv
import Scratch.DuhamelUp
import Scratch.PersistenceHm
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Time derivative of a high-regularity mild path in a lower `Ĥ^m`

A mild path in `C([0,T]; Ĥ^{k+1})` is identified, after inclusion to `Ĥ^m`
(`m ≤ k`), with the same-space heat-plus-Duhamel formula.  Its right
derivative in `Ĥ^m` along `[t0, T]` then follows from `HeatDeriv` and
`DuhamelDeriv.hasDerivWithinAt_duhνSame_Ici`. -/

open MeasureTheory Real Filter Topology Set
open scoped ENNReal

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
namespace MildTimeDeriv

open LerayHeat SobolevHilbert Duhamel HeatDeriv MildExistence
  PersistenceHm DuhamelDeriv

/-- Inclusion of the smoothing `duhHigh` integral is the same-space `duhνSame`. -/
lemma incl_duhHigh_to_duhνSame {k : ℕ} (hk : 2 ≤ k) {m : ℕ} (hm : m ≤ k)
    {ν t : ℝ} (hνt : 0 ≤ ν * t)
    {G : ℝ → Hm k} (hG : Continuous G) :
    incl (hm.trans (Nat.le_succ k)) (duhHigh hk ν G t) =
      duhνSame m ν (fun s => incl hm (G s)) t := by
  unfold duhHigh
  cases pred_succ_eq hk
  trans incl hm (incl (Nat.le_succ k) (duhν k ν G t))
  · exact (incl_comp (Nat.le_succ k) hm (duhν k ν G t)).symm
  · rw [incl_duhν_to_duhνSame k hνt hG, incl_duhνSame_of_le hm ν hG]

/-- The extended nonlinearity of a mild path, as a map `ℝ → Ĥ^k`. -/
def nsnExt {k : ℕ} (hk : 2 ≤ k) {T : ℝ} (hT : 0 ≤ T) (u : XTs k T) : ℝ → Hm k :=
  fun s => NSNsucc hk (ContinuousMap.IccExtend hT u s)

lemma continuous_nsnExt {k : ℕ} (hk : 2 ≤ k) {T : ℝ} (hT : 0 ≤ T) (u : XTs k T) :
    Continuous (nsnExt hk hT u) :=
  continuous_NSN_extUS hk hT u

/-- The included mild path equals the same-space heat-plus-Duhamel formula. -/
lemma mildS_eq_duhνSame {k : ℕ} (hk : 2 ≤ k) {m : ℕ} (hm : m ≤ k)
    {T ν : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    {u₀ : Hm (k + 1)} {u : XTs k T} (hu : IsMildS hk hT ν u₀ u)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    incl (hm.trans (Nat.le_succ k)) (u ⟨t, ht⟩) =
      heatH m (ν * t) (incl (hm.trans (Nat.le_succ k)) u₀) -
        duhνSame m ν (fun s => incl hm (nsnExt hk hT u s)) t := by
  have hνt : 0 ≤ ν * t := mul_nonneg hν.le ht.1
  set hle := hm.trans (Nat.le_succ k)
  have hU : u ⟨t, ht⟩ =
      heatH (k + 1) (ν * t) u₀ - duhHigh hk ν (nsnExt hk hT u) t := by
    simpa [nsnExt] using hu ⟨t, ht⟩
  have hheat :
      incl hle (heatH (k + 1) (ν * t) u₀) =
        heatH m (ν * t) (incl hle u₀) :=
    incl_heatH_of_le hle (ν * t) u₀
  have hduh :
      incl hle (duhHigh hk ν (nsnExt hk hT u) t) =
        duhνSame m ν (fun s => incl hm (nsnExt hk hT u s)) t :=
    incl_duhHigh_to_duhνSame hk hm hνt (continuous_nsnExt hk hT u)
  rw [hU, map_sub, hheat, hduh]

/-- Included extension of a mild path to all of `ℝ`. -/
def inclExt {k m : ℕ} (hle : m ≤ k + 1) {T : ℝ} (hT : 0 ≤ T) (u : XTs k T) :
    ℝ → Hm m :=
  fun t => incl hle (ContinuousMap.IccExtend hT u t)

lemma continuous_inclExt {k m : ℕ} (hle : m ≤ k + 1) {T : ℝ} (hT : 0 ≤ T)
    (u : XTs k T) : Continuous (inclExt hle hT u) :=
  (incl hle).continuous.comp (ContinuousMap.IccExtend hT u).continuous

lemma inclExt_of_mem {k m : ℕ} (hle : m ≤ k + 1) {T : ℝ} (hT : 0 ≤ T)
    (u : XTs k T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    inclExt hle hT u t = incl hle (u ⟨t, ht⟩) := by
  unfold inclExt
  rw [ContinuousMap.coe_IccExtend, Set.IccExtend_of_mem (h := hT) u ht]

lemma le_of_add_two_le {m k : ℕ} (hm2 : m + 2 ≤ k) : m ≤ k :=
  (Nat.le_add_right m 2).trans hm2

lemma le_succ_of_add_two_le {m k : ℕ} (hm2 : m + 2 ≤ k) : m ≤ k + 1 :=
  (le_of_add_two_le hm2).trans (Nat.le_succ k)

lemma add_two_le_succ {m k : ℕ} (hm2 : m + 2 ≤ k) : m + 2 ≤ k + 1 :=
  hm2.trans (Nat.le_succ k)

lemma heatOfHigh_incl {k m : ℕ} (hm2u : m + 2 ≤ k + 1) (u₀ : Hm (k + 1)) (σ : ℝ) :
    heatOfHigh m (incl hm2u u₀) σ =
      heatH m σ (incl (le_trans (incl_le_add_two m) hm2u) u₀) := by
  unfold heatOfHigh
  rw [incl_comp]

/-- Right derivative of the included mild path in `Ĥ^m`, along `[t0, T]`.
Requires one extra derivative on the source (`m + 2 ≤ k`) so that the
same-space Duhamel formula is differentiable in `Ĥ^m`. -/
theorem hasDerivWithinAt_mildS_incl
    {k : ℕ} (hk : 2 ≤ k) {m : ℕ} (hm2 : m + 2 ≤ k)
    {T ν : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    {u₀ : Hm (k + 1)} {u : XTs k T} (hu : IsMildS hk hT ν u₀ u)
    {t0 : ℝ} (ht0 : t0 ∈ Ico (0 : ℝ) T) :
    HasDerivWithinAt (inclExt (le_succ_of_add_two_le hm2) hT u)
      (ν • heatH m (ν * t0)
          (lapH m (incl (add_two_le_succ hm2) u₀)) -
        (incl (incl_le_add_two m)
            (incl hm2 (nsnExt hk hT u t0)) +
          ν • lapH m (duhνSame (m + 2) ν
            (fun s => incl hm2 (nsnExt hk hT u s)) t0)))
      (Icc t0 T) t0 := by
  have hm : m ≤ k := le_of_add_two_le hm2
  have hle : m ≤ k + 1 := le_succ_of_add_two_le hm2
  have hm2u : m + 2 ≤ k + 1 := add_two_le_succ hm2
  have ht0le : 0 ≤ t0 := ht0.1
  have ht0lt : t0 < T := ht0.2
  have hIcc_sub_Ici : Icc t0 T ⊆ Ici t0 := fun _ hx => hx.1
  have hIcc_sub_Ici0 : Icc t0 T ⊆ Ici (0 : ℝ) :=
    fun _ hx => le_trans ht0le hx.1
  have hIcc_sub_Icc : Icc t0 T ⊆ Icc (0 : ℝ) T :=
    fun _ hx => ⟨le_trans ht0le hx.1, hx.2⟩
  -- Heat factor: σ ↦ e^{νσ Δ} u₀, viewed in Ĥ^m.
  have hheat0 : HasDerivWithinAt
      (fun σ => heatOfHigh m (incl hm2u u₀) (ν * σ))
      (ν • heatH m (ν * t0) (lapH m (incl hm2u u₀)))
      (Ici (0 : ℝ)) t0 :=
    hasDerivWithinAt_heatH_visc m ν hν.le (incl hm2u u₀) ht0le
  have hheateq : (fun σ => heatOfHigh m (incl hm2u u₀) (ν * σ)) =
      fun σ => heatH m (ν * σ) (incl hle u₀) := by
    funext σ
    rw [heatOfHigh_incl]
  have hheat : HasDerivWithinAt
      (fun σ => heatH m (ν * σ) (incl hle u₀))
      (ν • heatH m (ν * t0) (lapH m (incl hm2u u₀)))
      (Icc t0 T) t0 := by
    have h := hheat0
    rw [hheateq] at h
    exact h.mono hIcc_sub_Ici0
  -- Duhamel factor in Ĥ^m, from a source in Ĥ^{m+2}.
  set G : ℝ → Hm (m + 2) := fun s => incl hm2 (nsnExt hk hT u s)
  have hG : Continuous G := (incl hm2).continuous.comp (continuous_nsnExt hk hT u)
  have hduh0 : HasDerivWithinAt
      (fun τ => duhνSame m ν (fun s => incl (incl_le_add_two m) (G s)) τ)
      (incl (incl_le_add_two m) (G t0) +
        ν • lapH m (duhνSame (m + 2) ν G t0))
      (Ici t0) t0 :=
    hasDerivWithinAt_duhνSame_Ici hν hG ht0le
  have hduheq : (fun τ => duhνSame m ν (fun s => incl (incl_le_add_two m) (G s)) τ) =
      fun τ => duhνSame m ν (fun s => incl hm (nsnExt hk hT u s)) τ := by
    funext τ
    refine congrArg (fun H => duhνSame m ν H τ) (funext fun s => ?_)
    exact incl_comp hm2 (incl_le_add_two m) (nsnExt hk hT u s)
  have hduh : HasDerivWithinAt
      (fun τ => duhνSame m ν (fun s => incl hm (nsnExt hk hT u s)) τ)
      (incl (incl_le_add_two m) (G t0) +
        ν • lapH m (duhνSame (m + 2) ν G t0))
      (Icc t0 T) t0 := by
    have h := hduh0
    rw [hduheq] at h
    exact h.mono hIcc_sub_Ici
  have hsum := hheat.sub hduh
  -- Identify the included path with heat minus Duhamel on `[t0, T]`.
  have heq : ∀ t ∈ Icc t0 T,
      inclExt hle hT u t =
        heatH m (ν * t) (incl hle u₀) -
          duhνSame m ν (fun s => incl hm (nsnExt hk hT u s)) t := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) T := hIcc_sub_Icc ht
    rw [inclExt_of_mem hle hT u ht']
    exact mildS_eq_duhνSame hk hm hν hT hu ht'
  exact hsum.congr_of_mem heq ⟨le_rfl, le_of_lt ht0lt⟩

/-- The explicit right-derivative formula for the included mild path. -/
def mildSDeriv {k : ℕ} (hk : 2 ≤ k) {m : ℕ} (hm2 : m + 2 ≤ k)
    {T ν : ℝ} (_hν : 0 < ν) (hT : 0 ≤ T)
    (u₀ : Hm (k + 1)) (u : XTs k T) (t : ℝ) : Hm m :=
  ν • heatH m (ν * t) (lapH m (incl (add_two_le_succ hm2) u₀)) -
    (incl (incl_le_add_two m) (incl hm2 (nsnExt hk hT u t)) +
      ν • lapH m (duhνSame (m + 2) ν
        (fun s => incl hm2 (nsnExt hk hT u s)) t))

lemma continuous_mildSDeriv {k : ℕ} (hk : 2 ≤ k) {m : ℕ} (hm2 : m + 2 ≤ k)
    {T ν : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (u₀ : Hm (k + 1)) (u : XTs k T) :
    Continuous (mildSDeriv hk hm2 hν hT u₀ u) := by
  have hG : Continuous fun s => incl hm2 (nsnExt hk hT u s) :=
    (incl hm2).continuous.comp (continuous_nsnExt hk hT u)
  have hheat : Continuous fun t =>
      heatH m (ν * t) (lapH m (incl (add_two_le_succ hm2) u₀)) :=
    continuous_heatH_comp (continuous_const_mul ν) continuous_const
  have hN : Continuous fun t =>
      incl (incl_le_add_two m) (incl hm2 (nsnExt hk hT u t)) :=
    (incl (incl_le_add_two m)).continuous.comp hG
  have hduh : Continuous fun t =>
      duhνSame (m + 2) ν (fun s => incl hm2 (nsnExt hk hT u s)) t :=
    (DuhamelUp.continuous_duh (continuous_scaleG hG)).comp (continuous_const_mul ν)
  exact (continuous_const.smul hheat).sub
    (hN.add (continuous_const.smul ((lapH m).continuous.comp hduh)))

lemma hasDerivWithinAt_mildSDeriv
    {k : ℕ} (hk : 2 ≤ k) {m : ℕ} (hm2 : m + 2 ≤ k)
    {T ν : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    {u₀ : Hm (k + 1)} {u : XTs k T} (hu : IsMildS hk hT ν u₀ u)
    {t0 : ℝ} (ht0 : t0 ∈ Ico (0 : ℝ) T) :
    HasDerivWithinAt (inclExt (le_succ_of_add_two_le hm2) hT u)
      (mildSDeriv hk hm2 hν hT u₀ u t0) (Icc t0 T) t0 :=
  hasDerivWithinAt_mildS_incl hk hm2 hν hT hu ht0

/-- The right derivative upgrades from `[t0, T]` to `[t0, ∞)` when `t0 < T`. -/
lemma hasDerivWithinAt_mildSDeriv_Ici
    {k : ℕ} (hk : 2 ≤ k) {m : ℕ} (hm2 : m + 2 ≤ k)
    {T ν : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    {u₀ : Hm (k + 1)} {u : XTs k T} (hu : IsMildS hk hT ν u₀ u)
    {t0 : ℝ} (ht0 : t0 ∈ Ico (0 : ℝ) T) :
    HasDerivWithinAt (inclExt (le_succ_of_add_two_le hm2) hT u)
      (mildSDeriv hk hm2 hν hT u₀ u t0) (Ici t0) t0 :=
  (hasDerivWithinAt_mildSDeriv hk hm2 hν hT hu ht0).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGE ht0.2)

/-- Averaging lemma: the interval average of a continuous path tends to its
value at the right endpoint, as the left endpoint tends to it from the left.
Isolated from the `Ĥᵐ` types. -/
lemma tendsto_intervalIntegral_avg {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {g : ℝ → E} (hg : Continuous g) (t0 : ℝ) :
    Tendsto (fun a : ℝ => (t0 - a)⁻¹ • ∫ s in a..t0, g s) (𝓝[<] t0) (𝓝 (g t0)) := by
  have hF : HasDerivAt (fun u => ∫ x in (t0 - 1)..u, g x) (g t0) t0 :=
    intervalIntegral.integral_hasDerivAt_right
      (hg.intervalIntegrable (t0 - 1) t0)
      (hg.stronglyMeasurableAtFilter volume (𝓝 t0)) hg.continuousAt
  have hslope := hF.tendsto_slope.mono_left (nhdsLT_le_nhdsNE t0)
  have hrew : ∀ᶠ a : ℝ in 𝓝[<] t0,
      slope (fun u => ∫ x in (t0 - 1)..u, g x) t0 a =
        (t0 - a)⁻¹ • ∫ s in a..t0, g s := by
    filter_upwards [eventually_mem_nhdsWithin] with a ha
    have hadj :=
      intervalIntegral.integral_add_adjacent_intervals (μ := volume) (f := g)
        (hg.intervalIntegrable (t0 - 1) t0) (hg.intervalIntegrable t0 a)
    rw [slope_def_module, ← hadj, add_sub_cancel_left, intervalIntegral.integral_symm,
      smul_neg, ← neg_smul, ← inv_neg, neg_sub]
  exact hslope.congr' hrew

/-- Two-sided derivative of the included mild path at an interior time. -/
theorem hasDerivAt_mildS_incl
    {k : ℕ} (hk : 2 ≤ k) {m : ℕ} (hm2 : m + 2 ≤ k)
    {T ν : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    {u₀ : Hm (k + 1)} {u : XTs k T} (hu : IsMildS hk hT ν u₀ u)
    {t0 : ℝ} (ht0 : t0 ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (inclExt (le_succ_of_add_two_le hm2) hT u)
      (mildSDeriv hk hm2 hν hT u₀ u t0) t0 := by
  set f := inclExt (le_succ_of_add_two_le hm2) hT u
  set g := mildSDeriv hk hm2 hν hT u₀ u
  have hg : Continuous g := continuous_mildSDeriv hk hm2 hν hT u₀ u
  have hf : Continuous f := continuous_inclExt _ hT u
  have hright : HasDerivWithinAt f (g t0) (Ici t0) t0 :=
    hasDerivWithinAt_mildSDeriv_Ici hk hm2 hν hT hu ⟨ht0.1.le, ht0.2⟩
  have hleft : HasDerivWithinAt f (g t0) (Iic t0) t0 := by
    rw [hasDerivWithinAt_iff_tendsto_slope, Iic_diff_right]
    have havg := tendsto_intervalIntegral_avg hg t0
    have hrew : ∀ᶠ a : ℝ in 𝓝[<] t0,
        (t0 - a)⁻¹ • ∫ s in a..t0, g s = slope f t0 a := by
      filter_upwards [Ioo_mem_nhdsLT ht0.1] with a ha
      have hlt : a < t0 := ha.2
      have ha0 : 0 < a := ha.1
      have hFTC : (∫ s in a..t0, g s) = f t0 - f a := by
        refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hlt.le
          hf.continuousOn (fun x hx => ?deriv) (hg.intervalIntegrable a t0)
        have hxIco : x ∈ Ico (0 : ℝ) T :=
          ⟨le_trans ha0.le (le_of_lt hx.1), lt_trans hx.2 ht0.2⟩
        exact (hasDerivWithinAt_mildSDeriv_Ici hk hm2 hν hT hu hxIco).Ioi_of_Ici
      rw [slope_def_module, hFTC, ← neg_sub t0 a, inv_neg, neg_smul, ← smul_neg, neg_sub]
    exact havg.congr' hrew
  simpa [Iic_union_Ici] using hleft.union hright

/-- On the half-open existence interval the included mild path is differentiable in the
one-sided sense at `t = 0`, and two-sided at every positive time. -/
theorem hasDerivWithinAt_mildS_incl_Ico
    {k : ℕ} (hk : 2 ≤ k) {m : ℕ} (hm2 : m + 2 ≤ k)
    {T ν : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    {u₀ : Hm (k + 1)} {u : XTs k T} (hu : IsMildS hk hT ν u₀ u)
    {t0 : ℝ} (ht0 : t0 ∈ Ico (0 : ℝ) T) :
    HasDerivWithinAt (inclExt (le_succ_of_add_two_le hm2) hT u)
      (mildSDeriv hk hm2 hν hT u₀ u t0) (Ico 0 T) t0 := by
  rcases eq_or_lt_of_le ht0.1 with h0 | hpos
  · subst h0
    exact (hasDerivWithinAt_mildSDeriv_Ici hk hm2 hν hT hu ht0).mono Ico_subset_Ici_self
  · exact (hasDerivAt_mildS_incl hk hm2 hν hT hu ⟨hpos, ht0.2⟩).hasDerivWithinAt.mono
      (subset_univ _)

/-- The included mild path is `C¹` on `[0, T)`. -/
theorem contDiffOn_one_inclExt
    {k : ℕ} (hk : 2 ≤ k) {m : ℕ} (hm2 : m + 2 ≤ k)
    {T ν : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    {u₀ : Hm (k + 1)} {u : XTs k T} (hu : IsMildS hk hT ν u₀ u) :
    ContDiffOn ℝ 1 (inclExt (le_succ_of_add_two_le hm2) hT u) (Ico 0 T) := by
  by_cases hTpos : 0 < T
  · rw [contDiffOn_one_iff_derivWithin (uniqueDiffOn_Ico (0 : ℝ) T)]
    refine ⟨?diff, ?cont⟩
    · intro t0 ht0
      exact (hasDerivWithinAt_mildS_incl_Ico hk hm2 hν hT hu ht0).differentiableWithinAt
    · have hder : ∀ t0 ∈ Ico (0 : ℝ) T,
          derivWithin (inclExt (le_succ_of_add_two_le hm2) hT u) (Ico 0 T) t0 =
            mildSDeriv hk hm2 hν hT u₀ u t0 :=
        fun t0 ht0 =>
          (hasDerivWithinAt_mildS_incl_Ico hk hm2 hν hT hu ht0).derivWithin
            (uniqueDiffOn_Ico (0 : ℝ) T t0 ht0)
      exact (continuous_mildSDeriv hk hm2 hν hT u₀ u).continuousOn.congr hder
  · have hempty : Ico (0 : ℝ) T = ∅ := Ico_eq_empty_iff.2 (not_lt.2 (le_of_not_gt hTpos))
    rw [hempty]
    exact contDiffOn_empty

#print axioms MildTimeDeriv.incl_duhHigh_to_duhνSame
#print axioms MildTimeDeriv.mildS_eq_duhνSame
#print axioms MildTimeDeriv.hasDerivWithinAt_mildS_incl
#print axioms MildTimeDeriv.continuous_mildSDeriv
#print axioms MildTimeDeriv.hasDerivAt_mildS_incl
#print axioms MildTimeDeriv.hasDerivWithinAt_mildS_incl_Ico
#print axioms MildTimeDeriv.contDiffOn_one_inclExt

end MildTimeDeriv
