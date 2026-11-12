import Scratch.LogBoundLocal
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Lipschitz / almost-everywhere form of the repaired tether rate

`FrohmanianTetherRateSmooth` asks for a right derivative of `M = ‖ω‖_∞` at every
time in `[0, T)`, with `M' ≤ C M² − κ M³`. This file records a Lipschitz / a.e.
form of the same rate, proves the comparison ceiling from that form, and
re-proves the reduction to `Clay_A_Fefferman`.

The Smooth form does *not* imply the Lipschitz form from the statements alone:
a finite right derivative with only an upper bound need not be locally Lipschitz
(the missing datum is a lower bound on the right derivative). The implication
is proved here under that extra local bound
(`frohmanianTetherRateLipschitz_of_smooth_of_locallyBddRightDeriv`). As a
statement about Fefferman solutions with no extra bound, the implication is
unsettled. The two forms are not equivalent: Lipschitz regularity gives a
two-sided derivative only almost everywhere, not a right derivative at every
time.

`FrohmanianTetherRateSmooth` and `Clay_A_Fefferman` are not edited. The Kato
maximal-solution assembly already on this branch
(`R3BKM.r3BKMContinuation_of_kato_of_log`, `LogBoundLocal.bkmLogInequality`) is
reused; no merge from `feat/r3-bkm-continuation` was needed.
-/

open MeasureTheory NavierStokes3D FrohmanianTether Set Filter
open scoped ContDiff NNReal Topology

noncomputable section
namespace RepairedTether

/-! ## The Lipschitz / a.e. rate -/

/-- **Repaired Frohmanian tether rate, Lipschitz / a.e. form** (OPEN for general
data). Along every local solution in Fefferman's smooth class from `u₀`,
`M = ‖ω‖_∞` is finite on `[0, T)`, locally Lipschitz on `[0, T)` (Lipschitz on
every compact `[0, b]` with `b < T`), and for a.e. `s ∈ (0, T)` it is two-sided
differentiable with `M'(s) ≤ C M(s)² − κ M(s)³`. The constants `C, κ > 0`
depend only on `u₀` and `ν`. -/
@[expose] public def FrohmanianTetherRateLipschitz (u₀ : VelocityField) (ν : ℝ) : Prop :=
  ∃ C kap : ℝ, 0 < C ∧ 0 < kap ∧
    ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsFeffermanSolutionOn ν T u₀ u p →
        (∀ t ∈ Ico (0 : ℝ) T, BddAbove (range fun x => ‖vorticity (u t) x‖)) ∧
        (∀ b ∈ Ico (0 : ℝ) T, ∃ K : ℝ≥0, LipschitzOnWith K (Mω u) (Icc (0 : ℝ) b)) ∧
        (∀ᵐ s, s ∈ Ioo (0 : ℝ) T →
          HasDerivAt (Mω u) (deriv (Mω u) s) s ∧
            deriv (Mω u) s ≤ C * Mω u s ^ 2 - kap * Mω u s ^ 3)

/-! ## Comparison for locally Lipschitz majorants -/

/-- For `C, κ > 0` and `C/κ ≤ x ≤ y`, the cubic majorant is nonincreasing. -/
theorem majorant_vector_field_antitoneOn
    {C kap x y : ℝ} (hC : 0 < C) (hκ : 0 < kap) (hx : C / kap ≤ x) (hxy : x ≤ y) :
    C * y ^ 2 - kap * y ^ 3 ≤ C * x ^ 2 - kap * x ^ 3 := by
  have hx0 : 0 ≤ x := le_trans (div_nonneg hC.le hκ.le) hx
  have hxy2 : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx0 hxy 2
  have hxφ : C - kap * x ≤ 0 := sub_nonpos.mpr <| by
    have : kap * (C / kap) ≤ kap * x := mul_le_mul_of_nonneg_left hx hκ.le
    rwa [mul_div_cancel₀ C hκ.ne'] at this
  have hyφ : C - kap * y ≤ C - kap * x := sub_le_sub_left (mul_le_mul_of_nonneg_left hxy hκ.le) _
  have hquad : y ^ 2 * (C - kap * y) ≤ x ^ 2 * (C - kap * x) := by
    have h1 : y ^ 2 * (C - kap * y) ≤ y ^ 2 * (C - kap * x) :=
      mul_le_mul_of_nonneg_left hyφ (sq_nonneg y)
    have h2 : y ^ 2 * (C - kap * x) ≤ x ^ 2 * (C - kap * x) :=
      mul_le_mul_of_nonpos_right hxy2 hxφ
    exact h1.trans h2
  calc C * y ^ 2 - kap * y ^ 3
      = y ^ 2 * (C - kap * y) := by ring
    _ ≤ x ^ 2 * (C - kap * x) := hquad
    _ = C * x ^ 2 - kap * x ^ 3 := by ring

/-- **Finite-horizon Riccati comparison, locally Lipschitz / a.e. form.**
If `M ≥ 0` is locally Lipschitz on `[0, T)` and `M' ≤ C M² − κ M³` almost
everywhere on `(0, T)`, then `M(t) ≤ max (M 0) (C/κ)` for every `t ∈ [0, T)`.
Lipschitz implies absolutely continuous, so the fundamental theorem identifies
`M(b) − M(a)` with `∫_a^b M'`. -/
theorem comparison_ode_stability_lipschitz
    (C kap : ℝ) (hC : 0 < C) (hκ : 0 < kap) (M : ℝ → ℝ) (T : ℝ)
    (hnonneg : ∀ τ ∈ Ico (0 : ℝ) T, 0 ≤ M τ)
    (hlip : ∀ b ∈ Ico (0 : ℝ) T, ∃ K : ℝ≥0, LipschitzOnWith K M (Icc (0 : ℝ) b))
    (hrate : ∀ᵐ s, s ∈ Ioo (0 : ℝ) T →
      HasDerivAt M (deriv M s) s ∧ deriv M s ≤ C * M s ^ 2 - kap * M s ^ 3)
    (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) :
    M t ≤ max (M 0) (C / kap) := by
  rcases ht.1.eq_or_lt with ht0 | _htpos
  · exact ht0.symm ▸ le_max_left (M 0) (C / kap)
  have _hnn0 : 0 ≤ M 0 := hnonneg 0 ⟨le_rfl, ht.1.trans_lt ht.2⟩
  set Y := max (M 0) (C / kap)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set Z := Y + ε
  have hbarrier : C / kap < Z :=
    lt_of_le_of_lt (le_max_right (M 0) (C / kap)) (lt_add_of_pos_right _ hε)
  have hM0 : M 0 ≤ Z :=
    (le_max_left (M 0) (C / kap)).trans (le_add_of_nonneg_right hε.le)
  obtain ⟨K, hMK⟩ := hlip t ht
  have hMcont : ContinuousOn M (Icc (0 : ℝ) t) := hMK.continuousOn
  by_contra hne
  have hMt : Z < M t := lt_of_not_ge hne
  let I : Set ℝ := Icc (0 : ℝ) t
  let S : Set I := {s | M (s : ℝ) ≤ Z}
  have hScl : IsClosed S :=
    isClosed_le (continuousOn_iff_continuous_restrict.mp hMcont) continuous_const
  haveI : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
  have hSc : IsCompact S := hScl.isCompact
  have hSne : S.Nonempty := ⟨⟨0, ⟨le_rfl, ht.1⟩⟩, hM0⟩
  obtain ⟨a, haS, haMax⟩ := hSc.exists_isMaxOn hSne continuous_subtype_val.continuousOn
  have haI : (a : ℝ) ∈ Icc (0 : ℝ) t := a.2
  have hMa_le : M (a : ℝ) ≤ Z := haS
  have hat : (a : ℝ) < t := by
    refine lt_of_le_of_ne haI.2 ?_
    intro heq
    have : M t ≤ Z := by simpa [heq] using hMa_le
    exact (not_le.mpr hMt) this
  have hMa : M (a : ℝ) = Z := by
    refine le_antisymm hMa_le ?_
    by_contra hlt'
    have hlt : M (a : ℝ) < Z := lt_of_not_ge hlt'
    have hopen : IsOpen {s : I | M (s : ℝ) < Z} :=
      isOpen_lt (continuousOn_iff_continuous_restrict.mp hMcont) continuous_const
    have haOpen : a ∈ {s : I | M (s : ℝ) < Z} := hlt
    obtain ⟨eps, epspos, hball⟩ := Metric.isOpen_iff.mp hopen a haOpen
    have hpos : 0 < min eps (t - (a : ℝ)) := lt_min epspos (sub_pos.mpr hat)
    set sR : ℝ := (a : ℝ) + min eps (t - (a : ℝ)) / 2
    have hs_gt : (a : ℝ) < sR := lt_add_of_pos_right _ (half_pos hpos)
    have hs_le : sR ≤ t := by
      have hle : min eps (t - (a : ℝ)) ≤ t - (a : ℝ) := min_le_right _ _
      have hhalf : min eps (t - (a : ℝ)) / 2 ≤ min eps (t - (a : ℝ)) :=
        half_le_self (le_min epspos.le (sub_pos.mpr hat).le)
      exact add_le_of_le_sub_left (hhalf.trans hle)
    have hsI : sR ∈ Icc (0 : ℝ) t := ⟨haI.1.trans hs_gt.le, hs_le⟩
    let s : I := ⟨sR, hsI⟩
    have hsdist : dist s a < eps := by
      rw [Subtype.dist_eq, Real.dist_eq]
      have : |sR - (a : ℝ)| = min eps (t - (a : ℝ)) / 2 := by
        simp [sR, abs_of_nonneg (half_pos hpos).le]
      rw [this]
      exact (half_lt_self hpos).trans_le (min_le_left _ _)
    have hsLt : M (s : ℝ) < Z := hball hsdist
    have : s ≤ a := haMax (show s ∈ S from hsLt.le)
    have : sR ≤ (a : ℝ) := this
    exact (not_le.mpr hs_gt) this
  have hIcc_sub : Icc (a : ℝ) t ⊆ Icc (0 : ℝ) t := Icc_subset_Icc haI.1 le_rfl
  have hlip_at : LipschitzOnWith K M (uIcc (a : ℝ) t) := by
    rw [uIcc_of_le haI.2]
    exact hMK.mono hIcc_sub
  have hac : AbsolutelyContinuousOnInterval M (a : ℝ) t :=
    hlip_at.absolutelyContinuousOnInterval
  have hFTC : ∫ s in (a : ℝ)..t, deriv M s = M t - M (a : ℝ) :=
    hac.integral_deriv_eq_sub
  have hφcont : ContinuousOn (fun s => C * M s ^ 2 - kap * M s ^ 3) (uIcc (a : ℝ) t) := by
    rw [uIcc_of_le haI.2]
    exact ((continuousOn_const.mul ((hMcont.mono hIcc_sub).pow 2)).sub
      (continuousOn_const.mul ((hMcont.mono hIcc_sub).pow 3)))
  have hinteriv : IntervalIntegrable (deriv M) MeasureTheory.volume (a : ℝ) t :=
    hac.intervalIntegrable_deriv
  have hintφ : IntervalIntegrable (fun s => C * M s ^ 2 - kap * M s ^ 3) MeasureTheory.volume (a : ℝ) t :=
    hφcont.intervalIntegrable
  have hintc : IntervalIntegrable (fun _ => C * Z ^ 2 - kap * Z ^ 3) MeasureTheory.volume (a : ℝ) t :=
    intervalIntegrable_const
  have hsing : (MeasureTheory.volume : Measure ℝ) {s | s = (a : ℝ) ∨ s = t} = 0 := by
    have : {s : ℝ | s = (a : ℝ) ∨ s = t} = ({(a : ℝ)} ∪ {t}) := by
      ext s; simp [or_comm]
    rw [this, measure_union (disjoint_singleton.2 hat.ne) (measurableSet_singleton t)]
    simp [measure_singleton]
  have hae : deriv M ≤ᵐ[MeasureTheory.volume.restrict (Icc (a : ℝ) t)]
      (fun s => C * M s ^ 2 - kap * M s ^ 3) := by
    change ∀ᵐ s ∂ MeasureTheory.volume.restrict (Icc (a : ℝ) t),
      deriv M s ≤ C * M s ^ 2 - kap * M s ^ 3
    rw [ae_restrict_iff' measurableSet_Icc]
    have hEnds : ∀ᵐ s : ℝ, s ≠ (a : ℝ) ∧ s ≠ t := by
      rw [ae_iff]
      have : {s : ℝ | ¬(s ≠ (a : ℝ) ∧ s ≠ t)} = {s | s = (a : ℝ) ∨ s = t} := by
        ext s
        constructor
        · intro h
          by_cases hsa : s = (a : ℝ)
          · exact Or.inl hsa
          · by_cases hst : s = t
            · exact Or.inr hst
            · exact (h ⟨hsa, hst⟩).elim
        · intro h happ
          exact h.elim happ.1 happ.2
      rwa [this]
    filter_upwards [hrate, hEnds] with s hsRate hs_ne hsIcc
    have hsIoo' : s ∈ Ioo (a : ℝ) t :=
      ⟨lt_of_le_of_ne hsIcc.1 hs_ne.1.symm, lt_of_le_of_ne hsIcc.2 hs_ne.2⟩
    have hsIoo : s ∈ Ioo (0 : ℝ) T :=
      ⟨lt_of_le_of_lt haI.1 hsIoo'.1, lt_trans hsIoo'.2 ht.2⟩
    exact (hsRate hsIoo).2
  have hle₁ : (∫ s in (a : ℝ)..t, deriv M s) ≤
      ∫ s in (a : ℝ)..t, (C * M s ^ 2 - kap * M s ^ 3) :=
    intervalIntegral.integral_mono_ae_restrict haI.2 hinteriv hintφ hae
  have hle₂ : (∫ s in (a : ℝ)..t, (C * M s ^ 2 - kap * M s ^ 3)) ≤
      ∫ s in (a : ℝ)..t, (C * Z ^ 2 - kap * Z ^ 3) := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo haI.2 hintφ hintc fun s hs => ?_
    have hsI : s ∈ Icc (0 : ℝ) t := ⟨haI.1.trans hs.1.le, hs.2.le⟩
    have hnotS : ¬ M s ≤ Z := fun hle =>
      (not_le.mpr hs.1) (haMax (show (⟨s, hsI⟩ : I) ∈ S from hle))
    exact majorant_vector_field_antitoneOn hC hκ hbarrier.le (le_of_not_ge hnotS)
  have hconst : (∫ s in (a : ℝ)..t, (C * Z ^ 2 - kap * Z ^ 3)) =
      (t - (a : ℝ)) * (C * Z ^ 2 - kap * Z ^ 3) := by
    simp [intervalIntegral.integral_const, smul_eq_mul]
  have hneg : C * Z ^ 2 - kap * Z ^ 3 < 0 :=
    AnalyticPipeline.majorant_vector_field_neg_of_gt hC hκ hbarrier
  have : M t - M (a : ℝ) < 0 := by
    have hstep : (t - (a : ℝ)) * (C * Z ^ 2 - kap * Z ^ 3) < 0 :=
      mul_neg_of_pos_of_neg (sub_pos.mpr hat) hneg
    calc M t - M (a : ℝ) = ∫ s in (a : ℝ)..t, deriv M s := hFTC.symm
      _ ≤ ∫ s in (a : ℝ)..t, (C * M s ^ 2 - kap * M s ^ 3) := hle₁
      _ ≤ ∫ s in (a : ℝ)..t, (C * Z ^ 2 - kap * Z ^ 3) := hle₂
      _ = (t - (a : ℝ)) * (C * Z ^ 2 - kap * Z ^ 3) := hconst
      _ < 0 := hstep
  rw [hMa] at this
  linarith

/-! ## Ceiling and Clay (A) from the Lipschitz rate -/

/-- Rate ⟹ uniform ceiling `max (M(u₀)) (C/κ)` on every local solution. -/
theorem ceiling_of_rateLipschitz {ν : ℝ} {u₀ : VelocityField}
    (h : FrohmanianTetherRateLipschitz u₀ ν) :
    ∃ Y : ℝ, ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsFeffermanSolutionOn ν T u₀ u p → ∀ t ∈ Ico (0 : ℝ) T,
        BddAbove (range fun x => ‖vorticity (u t) x‖) ∧ Mω u t ≤ Y := by
  obtain ⟨C, kap, hC, hκ, hr⟩ := h
  refine ⟨max (vorticity_sup_norm (vorticity u₀)) (C / kap), fun T u p hu t ht => ?_⟩
  obtain ⟨hb, hlip, hrate⟩ := hr T u p hu
  refine ⟨hb t ht, ?_⟩
  have hnn : ∀ τ ∈ Ico (0 : ℝ) T, 0 ≤ Mω u τ := fun τ _ => vorticity_sup_norm_nonneg _
  have := comparison_ode_stability_lipschitz C kap hC hκ (Mω u) T hnn hlip hrate t ht
  have hu0 : u 0 = u₀ := funext hu.2.2.2.1
  simpa [Mω, hu0] using this

/-- **Conditional theorem.** The conclusion is exactly Fefferman's Problem (A). -/
public theorem clay_A_fefferman_of_frohmanianTetherRateLipschitz
    (hrate : ∀ ν > (0 : ℝ), ∀ u₀ : VelocityField, ContDiff ℝ ∞ u₀ → (∀ x, div u₀ x = 0) →
      FeffermanDecay u₀ → FrohmanianTetherRateLipschitz u₀ ν)
    (hBKM : ∀ ν > (0 : ℝ), R3BKMContinuation ν) :
    Clay_A_Fefferman :=
  fun ν u₀ hν hs hd hdec =>
    hBKM ν hν u₀ hs hd hdec (ceiling_of_rateLipschitz (hrate ν hν u₀ hs hd hdec))

open R3BKM LogBoundLocal

/-- `Clay_A_Fefferman` from the Lipschitz rate and the Kato maximal solution.
The log-Sobolev input is the already-proved `bkmLogInequality` on this branch. -/
theorem clay_A_fefferman_of_rateLipschitz_of_kato
    (hrate : ∀ ν > (0 : ℝ), ∀ u₀ : VelocityField, ContDiff ℝ ∞ u₀ → (∀ x, div u₀ x = 0) →
      FeffermanDecay u₀ → FrohmanianTetherRateLipschitz u₀ ν)
    (hK : ∀ ν > (0 : ℝ), ∀ u₀ : VelocityField, ContDiff ℝ ∞ u₀ → (∀ x, div u₀ x = 0) →
      FeffermanDecay u₀ → KatoMaximalSolution ν u₀) :
    Clay_A_Fefferman :=
  clay_A_fefferman_of_frohmanianTetherRateLipschitz hrate
    fun ν hν => r3BKMContinuation_of_kato_of_log bkmLogInequality (hK ν hν)

/-! ## Non-vacuity at `u₀ = 0`, and Smooth → Lipschitz under a local bound -/

/-- Hypothesis `FrohmanianTetherRateLipschitz` holds at `u₀ = 0`. -/
theorem frohmanianTetherRateLipschitz_zero (ν : ℝ) : FrohmanianTetherRateLipschitz 0 ν := by
  refine ⟨1, 1, one_pos, one_pos, fun T u p hu => ?_⟩
  have hz : ∀ τ ∈ Ico (0 : ℝ) T, Mω u τ = 0 := fun τ hτ => by
    simp only [Mω]
    rw [eq_zero_of_isFeffermanSolutionOn_zero hu τ hτ, ClayStatements.vorticity_sup_norm_zero_field]
  refine ⟨fun t ht => ?_, fun b hb => ?_, ?_⟩
  · rw [eq_zero_of_isFeffermanSolutionOn_zero hu t ht]
    refine ⟨0, ?_⟩
    rintro _ ⟨x, rfl⟩
    simp [vorticity, curl_zero]
  · refine ⟨0, (lipschitzOnWith_iff_dist_le_mul).2 ?_⟩
    intro s hs τ hτ
    have hs0 : Mω u s = 0 := hz s ⟨hs.1, lt_of_le_of_lt hs.2 hb.2⟩
    have hτ0 : Mω u τ = 0 := hz τ ⟨hτ.1, lt_of_le_of_lt hτ.2 hb.2⟩
    simp [Real.dist_eq, hs0, hτ0]
  · refine Filter.Eventually.of_forall fun s hs => ?_
    have hev : Mω u =ᶠ[nhds s] fun _ => (0 : ℝ) := by
      have hnhds : Ico (0 : ℝ) T ∈ nhds s := Ico_mem_nhds hs.1 hs.2
      filter_upwards [hnhds] with τ hτ
      exact hz τ hτ
    have hder : HasDerivAt (Mω u) 0 s :=
      (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq hev
    have hderiv0 : deriv (Mω u) s = 0 := hder.deriv
    refine ⟨hderiv0 ▸ hder, ?_⟩
    rw [hderiv0, hz s ⟨hs.1.le, hs.2⟩]
    norm_num

/-- A continuous path with a right derivative bounded in absolute value on `[a, b)`
is Lipschitz on `[a, b]`. -/
theorem lipschitzOnWith_of_bdd_right_deriv
    {M : ℝ → ℝ} {K a b : ℝ} (hK : 0 ≤ K)
    (hcont : ContinuousOn M (Icc a b))
    (hderiv : ∀ s ∈ Ico a b, ∃ d : ℝ, HasDerivWithinAt M d (Ici s) s ∧ |d| ≤ K) :
    LipschitzOnWith ⟨K, hK⟩ M (Icc a b) := by
  refine (lipschitzOnWith_iff_dist_le_mul).2 ?_
  intro x hx y hy
  wlog hxy : x ≤ y generalizing x y
  · have := this y hy x hx (le_of_not_ge hxy)
    simpa [dist_comm] using this
  change |M x - M y| ≤ K * |x - y|
  rw [abs_sub_le_iff, abs_sub_comm x y, abs_of_nonneg (sub_nonneg.mpr hxy)]
  have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
  have hcontxy : ContinuousOn M (Icc x y) := hcont.mono hsub
  have hright : ∀ s ∈ Ico x y, ∃ d : ℝ, HasDerivWithinAt M d (Ici s) s ∧ |d| ≤ K :=
    fun s hs => hderiv s ⟨hx.1.trans hs.1, hs.2.trans_le hy.2⟩
  let f' : ℝ → ℝ := fun s =>
    if hs : s ∈ Ico x y then Classical.choose (hright s hs) else 0
  have hf' : ∀ s ∈ Ico x y, HasDerivWithinAt M (f' s) (Ici s) s ∧ |f' s| ≤ K := by
    intro s hs
    dsimp only [f']
    rw [dif_pos hs]
    exact Classical.choose_spec (hright s hs)
  have hmul : ∀ s, HasDerivAt (fun τ => K * (τ - x)) K s := fun s => by
    have h := ((hasDerivAt_id s).sub_const x).const_mul K
    have hK1 : K * 1 = K := mul_one K
    rwa [hK1] at h
  have hB : ∀ s, HasDerivAt (fun τ => M x + K * (τ - x)) K s := fun s => by
    have hadd := (hasDerivAt_const s (M x)).add (hmul s)
    have heq : (fun τ => M x + K * (τ - x)) =ᶠ[nhds s]
        ((fun _ : ℝ => M x) + fun τ => K * (τ - x)) :=
      Filter.Eventually.of_forall fun τ => by simp [Pi.add_apply]
    have hadd' := hadd.congr_of_eventuallyEq heq
    have hsum : (0 : ℝ) + K = K := zero_add K
    rwa [hsum] at hadd'
  have hBm : ∀ s, HasDerivAt (fun τ => -(M x) + K * (τ - x)) K s := fun s => by
    have hadd := (hasDerivAt_const s (-(M x))).add (hmul s)
    have heq : (fun τ => -(M x) + K * (τ - x)) =ᶠ[nhds s]
        ((fun _ : ℝ => -(M x)) + fun τ => K * (τ - x)) :=
      Filter.Eventually.of_forall fun τ => by simp [Pi.add_apply]
    have hadd' := hadd.congr_of_eventuallyEq heq
    have hsum : (0 : ℝ) + K = K := zero_add K
    rwa [hsum] at hadd'
  have hBcont : ContinuousOn (fun τ => M x + K * (τ - x)) (Icc x y) :=
    (continuous_const.add (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn
  have hBmcont : ContinuousOn (fun τ => -(M x) + K * (τ - x)) (Icc x y) :=
    (continuous_const.add (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn
  constructor
  · -- `M x - M y ≤ K * (y - x)`
    have hle := image_le_of_deriv_right_le_deriv_boundary
      (f := fun τ => -M τ) (f' := fun s => -f' s)
      hcontxy.neg (fun s hs => (hf' s hs).1.neg)
      (B := fun τ => -(M x) + K * (τ - x)) (B' := fun _ => K)
      (le_of_eq (by ring)) hBmcont (fun s _ => (hBm s).hasDerivWithinAt)
      (fun s hs => by have := (abs_le.mp (hf' s hs).2).1; linarith)
      (x := y) ⟨hxy, le_rfl⟩
    linarith
  · -- `M y - M x ≤ K * (y - x)`
    have hle := image_le_of_deriv_right_le_deriv_boundary (f := M) (f' := f')
      hcontxy (fun s hs => (hf' s hs).1)
      (B := fun τ => M x + K * (τ - x)) (B' := fun _ => K)
      (le_of_eq (by ring)) hBcont (fun s _ => (hB s).hasDerivWithinAt)
      (fun s hs => (abs_le.mp (hf' s hs).2).2) (x := y) ⟨hxy, le_rfl⟩
    linarith

/-- If, in addition to `FrohmanianTetherRateSmooth`, the right derivative of `Mω`
is locally bounded on every compact `[0, b] ⊂ [0, T)`, then the Lipschitz / a.e.
rate holds, with the same constants. The local bound is not part of
`FrohmanianTetherRateSmooth`. -/
theorem frohmanianTetherRateLipschitz_of_smooth_of_locallyBddRightDeriv
    {u₀ : VelocityField} {ν : ℝ}
    (h : FrohmanianTetherRateSmooth u₀ ν)
    (hbdd : ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsFeffermanSolutionOn ν T u₀ u p →
        ∀ b ∈ Ico (0 : ℝ) T, ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Ico (0 : ℝ) b,
          ∀ d, HasDerivWithinAt (Mω u) d (Ici s) s → |d| ≤ K) :
    FrohmanianTetherRateLipschitz u₀ ν := by
  obtain ⟨C, kap, hC, hκ, hr⟩ := h
  refine ⟨C, kap, hC, hκ, fun T u p hu => ?_⟩
  obtain ⟨hc, hd, hb⟩ := hr T u p hu
  refine ⟨hb, ?_, ?_⟩
  · intro b hbT
    obtain ⟨K, hK, hKb⟩ := hbdd T u p hu b hbT
    have hcont : ContinuousOn (Mω u) (Icc (0 : ℝ) b) :=
      hc.mono fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 hbT.2⟩
    refine ⟨⟨K, hK⟩, lipschitzOnWith_of_bdd_right_deriv hK hcont ?_⟩
    intro s hs
    obtain ⟨d, hd', _⟩ := hd s ⟨hs.1, lt_trans hs.2 hbT.2⟩
    exact ⟨d, hd', hKb s hs d hd'⟩
  · -- Rademacher on each `[0, b]`, `b < T`, glued over a countable exhaustion of `(0, T)`.
    have hpoint : ∀ b ∈ Ico (0 : ℝ) T, ∀ᵐ s, s ∈ Ioo (0 : ℝ) b →
        HasDerivAt (Mω u) (deriv (Mω u) s) s ∧
          deriv (Mω u) s ≤ C * Mω u s ^ 2 - kap * Mω u s ^ 3 := by
      intro b hbT
      obtain ⟨K, hK, hKb⟩ := hbdd T u p hu b hbT
      have hcont : ContinuousOn (Mω u) (Icc (0 : ℝ) b) :=
        hc.mono fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 hbT.2⟩
      have hlip : LipschitzOnWith ⟨K, hK⟩ (Mω u) (Icc (0 : ℝ) b) :=
        lipschitzOnWith_of_bdd_right_deriv hK hcont fun s hs => by
          obtain ⟨d, hd', _⟩ := hd s ⟨hs.1, lt_trans hs.2 hbT.2⟩
          exact ⟨d, hd', hKb s hs d hd'⟩
      filter_upwards [hlip.ae_differentiableWithinAt_of_mem (μ := MeasureTheory.volume)] with s hdiff hsIoo
      have hsIcc : s ∈ Icc (0 : ℝ) b := Ioo_subset_Icc_self hsIoo
      have hnhds : Icc (0 : ℝ) b ∈ nhds s := Icc_mem_nhds hsIoo.1 hsIoo.2
      have hAt : DifferentiableAt ℝ (Mω u) s := (hdiff hsIcc).differentiableAt hnhds
      have hHas : HasDerivAt (Mω u) (deriv (Mω u) s) s := hAt.hasDerivAt
      obtain ⟨d, hdright, hdle⟩ := hd s ⟨hsIoo.1.le, lt_trans hsIoo.2 hbT.2⟩
      have huniq : deriv (Mω u) s = d :=
        (uniqueDiffWithinAt_Ici s).eq_deriv (Ici s)
          (hHas.hasDerivWithinAt (s := Ici s)) hdright
      exact ⟨hHas, huniq ▸ hdle⟩
    -- Exhaust `(0, T)` by the intervals `(0, T * (n+1)/(n+2))` when `T > 0`.
    by_cases hT : T ≤ 0
    · have : Ioo (0 : ℝ) T = ∅ := Ioo_eq_empty_of_le hT
      refine Filter.Eventually.of_forall fun s hs => (this ▸ hs).elim
    · have hTpos : 0 < T := lt_of_not_ge hT
      let b : ℕ → ℝ := fun n => T * ((n + 1 : ℝ) / (n + 2 : ℝ))
      have hbIco : ∀ n, b n ∈ Ico (0 : ℝ) T := fun n => by
        have hn1 : 0 < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos _
        have hn2 : 0 < (n + 2 : ℝ) := by exact_mod_cast (Nat.succ_pos (n + 1))
        have hfrac : 0 < (n + 1 : ℝ) / (n + 2 : ℝ) := div_pos hn1 hn2
        have hfraclt : (n + 1 : ℝ) / (n + 2 : ℝ) < 1 :=
          (div_lt_one hn2).2 (by linarith)
        exact ⟨mul_nonneg hTpos.le hfrac.le, mul_lt_of_lt_one_right hTpos hfraclt⟩
      have hall : ∀ n, ∀ᵐ s, s ∈ Ioo (0 : ℝ) (b n) →
          HasDerivAt (Mω u) (deriv (Mω u) s) s ∧
            deriv (Mω u) s ≤ C * Mω u s ^ 2 - kap * Mω u s ^ 3 :=
        fun n => hpoint (b n) (hbIco n)
      have hall' : ∀ᵐ s, ∀ n, s ∈ Ioo (0 : ℝ) (b n) →
          HasDerivAt (Mω u) (deriv (Mω u) s) s ∧
            deriv (Mω u) s ≤ C * Mω u s ^ 2 - kap * Mω u s ^ 3 :=
        (MeasureTheory.ae_all_iff).2 hall
      filter_upwards [hall'] with s hs hsIoo
      have hspos : 0 < s := hsIoo.1
      have hsT : s < T := hsIoo.2
      -- Choose `n` large enough that `s < T * (n+1)/(n+2)`.
      have hfrac : s / T < 1 := (div_lt_one hTpos).2 hsT
      obtain ⟨n, hn⟩ : ∃ n : ℕ, s / T < (n + 1 : ℝ) / (n + 2 : ℝ) := by
        have htend : Tendsto (fun n : ℕ => (n + 1 : ℝ) / (n + 2 : ℝ)) atTop (nhds (1 : ℝ)) := by
          have heq : (fun n : ℕ => (n + 1 : ℝ) / (n + 2 : ℝ)) =
              fun n : ℕ => (1 : ℝ) - 1 / (n + 2 : ℝ) := by
            ext n; field_simp; ring
          have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 2 : ℝ)) atTop (nhds (0 : ℝ)) := by
            simpa [one_div] using tendsto_inv_atTop_zero.comp
              (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
          rw [heq]
          simpa using tendsto_const_nhds.sub hinv
        exact ((tendsto_order.1 htend).1 _ hfrac).exists
      have hsb : s < b n := by
        have : s < T * ((n + 1 : ℝ) / (n + 2 : ℝ)) := by
          rw [mul_comm]
          exact (div_lt_iff₀ hTpos).mp hn
        simpa [b] using this
      exact hs n ⟨hspos, hsb⟩

end RepairedTether

#print axioms RepairedTether.comparison_ode_stability_lipschitz
#print axioms RepairedTether.ceiling_of_rateLipschitz
#print axioms RepairedTether.clay_A_fefferman_of_frohmanianTetherRateLipschitz
#print axioms RepairedTether.clay_A_fefferman_of_rateLipschitz_of_kato
#print axioms RepairedTether.frohmanianTetherRateLipschitz_zero
#print axioms RepairedTether.lipschitzOnWith_of_bdd_right_deriv
#print axioms RepairedTether.frohmanianTetherRateLipschitz_of_smooth_of_locallyBddRightDeriv
#print axioms RepairedTether.majorant_vector_field_antitoneOn
