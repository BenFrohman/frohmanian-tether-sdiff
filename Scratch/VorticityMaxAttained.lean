import Scratch.TetherRateDerivation
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Attainment of the vorticity maximum, and Danskin / Rademacher regularity of `M(t)`

This file proves the strongest honest forms of the first two named inequalities from
`Scratch/TetherRateDerivation.lean`, and records the mismatches with those `Prop`s as
stated.

* `VorticityMaximumAttained` as written has no decay hypothesis. It is not implied by
  `IsFeffermanSolutionOn` (kernel-checked disproof: a smooth stationary Euler shear with
  `ν = 0`, whose vorticity is `(0,0,-arctan y)` and never attains its supremum). The
  energy inequality in `IsFeffermanSolutionOn` does not force finite energy, nor spatial
  decay of snapshots, nor `ν > 0`.
* A continuous nonnegative function on `ℝ³` that tends to `0` at infinity *does* attain
  its global maximum. `FeffermanDecay` of a snapshot implies that its vorticity tends to
  `0` at infinity, hence a maximizer exists. Under that hypothesis on every snapshot
  `u(t)` for `t ∈ [0, T)`, a (choice) trajectory `x_max` realizing
  `VorticityMaximumAttained u T x_max` exists. Fefferman (A) supplies `FeffermanDecay`
  of the *initial* datum `u₀`, and therefore attainment at `t = 0`; it does not, as
  formalized, supply decay of later snapshots.
* `DifferentiableMaximizer` asks for a differentiable-in-time selection of maximizers.
  Attainment does not give this: a maximizing trajectory can jump when two peaks trade
  heights, so no continuous (hence no differentiable) selection need exist. The
  derivation does not need path regularity of `x_max`. What it needs is regularity of
  `M(t) = ‖ω(t)‖_∞` itself.
* If the time derivative of `ω` is bounded uniformly in space on a compact time interval
  where `|ω|` is bounded, then `M` is Lipschitz there, hence differentiable almost
  everywhere (Rademacher). At every two-sided differentiability point with `M(t) > 0`,
  Danskin's identity holds at *every* maximizer, and therefore `DanskinRateAt` holds
  there. A uniform-in-space bound on `∂t ω` is *not* supplied by
  `IsFeffermanSolutionOn` alone (joint smoothness does not give bounds uniform in `x`).

Strain control (inequality 3) and direction coercivity (inequality 4) remain
unsettled along Fefferman solutions. The original `FrohmanianTetherRateSmooth` is
unchanged and remains unsettled for general data.

Status convention: every claim is kernel-checked proved, kernel-checked disproved,
or explicitly unsettled.
-/

open MeasureTheory NavierStokes3D FrohmanianTether
open RepairedTether TetherRateDerivation Filter
open scoped InnerProductSpace ContDiff Topology NNReal

noncomputable section
namespace VorticityMaxAttained

/-! ## 1. Attainment for a continuous nonnegative function vanishing at infinity -/

/-- A continuous nonnegative function `ℝ³ → ℝ` that tends to `0` at infinity attains a
global maximum. (Nonnegativity is used: a negative function approaching `0` need not
attain its supremum `0`.) -/
theorem exists_isMaxOn_of_tendsto_zero {f : T3 → ℝ} (hf : Continuous f)
    (hnn : ∀ x, 0 ≤ f x)
    (h0 : Tendsto f (cocompact T3) (nhds (0 : ℝ))) :
    ∃ x : T3, IsMaxOn f Set.univ x := by
  by_cases htriv : ∀ x, f x = 0
  · refine ⟨0, fun y _ => ?_⟩
    simp [htriv y, htriv 0]
  · push_neg at htriv
    obtain ⟨x0, hx0ne⟩ := htriv
    have hx0 : 0 < f x0 := lt_of_le_of_ne (hnn x0) (Ne.symm hx0ne)
    have hst : ∀ᶠ y in cocompact T3, f y < f x0 := by
      have : {y : ℝ | dist y (0 : ℝ) < f x0} ∈ nhds (0 : ℝ) :=
        Metric.ball_mem_nhds 0 hx0
      filter_upwards [h0 this] with y hy
      have : |f y| < f x0 := by
        simpa [Real.dist_eq, sub_zero] using hy
      exact (le_abs_self (f y)).trans_lt this
    obtain ⟨K, hK, hKc⟩ := mem_cocompact.mp hst
    let K' := K ∪ {x0}
    have hK' : IsCompact K' := hK.union isCompact_singleton
    have hne : K'.Nonempty := ⟨x0, Or.inr rfl⟩
    obtain ⟨x, hxK', hmax⟩ := hK'.exists_isMaxOn hne hf.continuousOn
    refine ⟨x, fun y _ => ?_⟩
    by_cases hy : y ∈ K'
    · exact isMaxOn_iff.mp hmax y hy
    · have hyK : y ∉ K := fun h => hy (Or.inl h)
      exact (hKc hyK).le.trans (isMaxOn_iff.mp hmax x0 (Or.inr rfl))

/-- Continuous `|ω|` that tends to `0` at infinity attains a global spatial maximum. -/
theorem exists_isMaxOn_norm_vorticity_of_tendsto_zero {omega : VelocityField}
    (hc : Continuous fun y => ‖omega y‖)
    (h0 : Tendsto (fun y => ‖omega y‖) (cocompact T3) (nhds (0 : ℝ))) :
    ∃ x : T3, IsMaxOn (fun y => ‖omega y‖) Set.univ x :=
  exists_isMaxOn_of_tendsto_zero hc (fun _ => norm_nonneg _) h0

/-- An attained spatial maximum of `|ω|` is a genuine `L∞` representative:
the range is bounded and `‖ω‖_∞ = |ω(x)|`. -/
theorem isMaxOn_vorticity_sup_norm_eq {omega : VorticityField} {x : T3}
    (h : IsMaxOn (fun y => ‖omega y‖) Set.univ x) :
    BddAbove (Set.range fun y => ‖omega y‖) ∧
      vorticity_sup_norm omega = ‖omega x‖ := by
  have hbdd : BddAbove (Set.range fun y => ‖omega y‖) :=
    ⟨‖omega x‖, by rintro _ ⟨y, rfl⟩; exact h (Set.mem_univ y)⟩
  refine ⟨hbdd, le_antisymm ?_ ?_⟩
  · exact ciSup_le fun y => h (Set.mem_univ y)
  · exact le_ciSup hbdd x

/-! ## 2. Continuity of vorticity, and `FeffermanDecay` ⇒ vanish at infinity -/

lemma euclidean_norm_le_sum_abs (v : EuclideanSpace ℝ (Fin 3)) :
    ‖v‖ ≤ ∑ i : Fin 3, |v i| := by
  have hsum : ∑ i : Fin 3, |v i| = |v 0| + |v 1| + |v 2| := by
    simp [Fin.sum_univ_three]
  have hnorm : ‖v‖ ^ 2 = ∑ i : Fin 3, |v i| ^ 2 := by
    simpa [Real.norm_eq_abs] using PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) v
  have hsqs : ∑ i : Fin 3, |v i| ^ 2 = |v 0| ^ 2 + |v 1| ^ 2 + |v 2| ^ 2 := by
    simp [Fin.sum_univ_three]
  have hele : |v 0| ^ 2 + |v 1| ^ 2 + |v 2| ^ 2 ≤ (|v 0| + |v 1| + |v 2|) ^ 2 := by
    nlinarith [mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 1)),
      mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 2)),
      mul_nonneg (abs_nonneg (v 1)) (abs_nonneg (v 2))]
  have : ‖v‖ ^ 2 ≤ (∑ i : Fin 3, |v i|) ^ 2 := by
    rw [hnorm, hsqs, hsum]
    exact hele
  exact (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)).mp this

lemma fderiv_coord_apply (u : VelocityField) (x : T3) (i : Fin 3) (v : T3)
    (hu : DifferentiableAt ℝ u x) :
    (fderiv ℝ (fun y => u y i) x) v = ((fderiv ℝ u x) v) i := by
  have hfun : (fun y => u y i) =
      ((PiLp.proj (p := 2) (fun _ : Fin 3 => ℝ) i : T3 →L[ℝ] ℝ)) ∘ u := rfl
  have h :=
    (((PiLp.proj (p := 2) (fun _ : Fin 3 => ℝ) i : T3 →L[ℝ] ℝ)).hasFDerivAt).comp
      x hu.hasFDerivAt
  rw [hfun, h.fderiv]
  rfl

lemma norm_fderiv_coord_le (u : VelocityField) (x : T3) (i : Fin 3) (v : T3)
    (hu : DifferentiableAt ℝ u x) :
    ‖(fderiv ℝ (fun y => u y i) x) v‖ ≤ ‖fderiv ℝ u x‖ * ‖v‖ := by
  rw [fderiv_coord_apply u x i v hu, Real.norm_eq_abs]
  have hpi : |((fderiv ℝ u x) v) i| ≤ ‖(fderiv ℝ u x) v‖ :=
    (PiLp.norm_apply_le (p := 2) (fderiv ℝ u x v) i)
  exact hpi.trans ((fderiv ℝ u x).le_opNorm v)

lemma directionalCoord_le_fderiv (u : VelocityField) (comp dir : Fin 3) (x : T3)
    (hu : DifferentiableAt ℝ u x) :
    |directionalCoord u comp dir x| ≤ ‖fderiv ℝ u x‖ := by
  unfold directionalCoord
  have := norm_fderiv_coord_le u x comp (EuclideanSpace.single dir (1 : ℝ)) hu
  have h1 : ‖EuclideanSpace.single dir (1 : ℝ)‖ = 1 := by
    simp [PiLp.norm_single]
  simpa [Real.norm_eq_abs, h1] using this

theorem curl_apply (u : VelocityField) (x : T3) :
    curl u x 0 = directionalCoord u 2 1 x - directionalCoord u 1 2 x ∧
    curl u x 1 = directionalCoord u 0 2 x - directionalCoord u 2 0 x ∧
    curl u x 2 = directionalCoord u 1 0 x - directionalCoord u 0 1 x := by
  unfold curl
  constructor
  · simp [PiLp.add_apply, PiLp.single_apply]
  constructor
  · simp [PiLp.add_apply, PiLp.single_apply]
  · simp [PiLp.add_apply, PiLp.single_apply]

/-- `‖curl u(x)‖ ≤ 6 ‖Du(x)‖` at a differentiable point. -/
theorem norm_curl_le_six_fderiv (u : VelocityField) (x : T3)
    (hu : DifferentiableAt ℝ u x) :
    ‖curl u x‖ ≤ 6 * ‖fderiv ℝ u x‖ := by
  have hterm (comp dir : Fin 3) : |directionalCoord u comp dir x| ≤ ‖fderiv ℝ u x‖ :=
    directionalCoord_le_fderiv u comp dir x hu
  have hx0 : |curl u x 0| ≤ 2 * ‖fderiv ℝ u x‖ := by
    rw [(curl_apply u x).1]
    exact (abs_sub _ _).trans (by linarith [hterm 2 1, hterm 1 2])
  have hx1 : |curl u x 1| ≤ 2 * ‖fderiv ℝ u x‖ := by
    rw [(curl_apply u x).2.1]
    exact (abs_sub _ _).trans (by linarith [hterm 0 2, hterm 2 0])
  have hx2 : |curl u x 2| ≤ 2 * ‖fderiv ℝ u x‖ := by
    rw [(curl_apply u x).2.2]
    exact (abs_sub _ _).trans (by linarith [hterm 1 0, hterm 0 1])
  have hsum : ∑ i : Fin 3, |curl u x i| ≤ 6 * ‖fderiv ℝ u x‖ := by
    rw [Fin.sum_univ_three]
    linarith [hx0, hx1, hx2]
  exact (euclidean_norm_le_sum_abs (curl u x)).trans hsum

lemma opNorm_fderiv_le_sum_basis (u : VelocityField) (x : T3) :
    ‖fderiv ℝ u x‖ ≤
      ∑ i : Fin 3, ‖(fderiv ℝ u x) (EuclideanSpace.single i (1 : ℝ))‖ := by
  refine (fderiv ℝ u x).opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    fun v => ?_
  have hv : v = ∑ i : Fin 3, v i • EuclideanSpace.single i (1 : ℝ) := by
    simpa [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v).symm
  calc
    ‖(fderiv ℝ u x) v‖
        = ‖(fderiv ℝ u x) (∑ i : Fin 3, v i • EuclideanSpace.single i (1 : ℝ))‖ := by
          rw [← hv]
    _ = ‖∑ i : Fin 3, v i • (fderiv ℝ u x) (EuclideanSpace.single i (1 : ℝ))‖ := by
          simp [map_sum, map_smul]
    _ ≤ ∑ i : Fin 3, ‖v i • (fderiv ℝ u x) (EuclideanSpace.single i (1 : ℝ))‖ :=
          norm_sum_le _ _
    _ = ∑ i : Fin 3, |v i| * ‖(fderiv ℝ u x) (EuclideanSpace.single i (1 : ℝ))‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i : Fin 3, ‖v‖ * ‖(fderiv ℝ u x) (EuclideanSpace.single i (1 : ℝ))‖ := by
          refine Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          rw [← Real.norm_eq_abs]
          exact PiLp.norm_apply_le _ _
    _ = (∑ i : Fin 3, ‖(fderiv ℝ u x) (EuclideanSpace.single i (1 : ℝ))‖) * ‖v‖ := by
          simp [mul_comm, Finset.mul_sum]

/-- `FeffermanDecay` gives an algebraic decay bound on `‖Du(x)‖`. -/
theorem fderiv_bound_of_feffermanDecay {f : VelocityField} (h : FeffermanDecay f) (K : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : T3, ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ (-K) := by
  have hα : ∀ i : Fin 3, ∃ C : ℝ, ∀ x : T3,
      ‖iteratedFDeriv ℝ 1 f x (fun _ => EuclideanSpace.single i (1 : ℝ))‖ ≤
        C * (1 + ‖x‖) ^ (-K) := fun i => h 1 (fun _ => i) K
  choose C0 hC0 using hα
  let C : Fin 3 → ℝ := fun i => max (C0 i) 0
  have hC : ∀ i x,
      ‖iteratedFDeriv ℝ 1 f x (fun _ => EuclideanSpace.single i (1 : ℝ))‖ ≤
        C i * (1 + ‖x‖) ^ (-K) := fun i x =>
    (hC0 i x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  refine ⟨∑ i : Fin 3, C i, Finset.sum_nonneg fun i _ => le_max_right _ _, fun x => ?_⟩
  have hsum :
      ‖fderiv ℝ f x‖ ≤ ∑ i : Fin 3, C i * (1 + ‖x‖) ^ (-K) := by
    refine (opNorm_fderiv_le_sum_basis f x).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    simpa [iteratedFDeriv_one_apply] using hC i x
  have hfactor :
      ∑ i : Fin 3, C i * (1 + ‖x‖) ^ (-K) =
        (∑ i : Fin 3, C i) * (1 + ‖x‖) ^ (-K) := by
    simp [Finset.sum_mul]
  exact hsum.trans_eq hfactor

theorem continuous_directionalCoord {u : VelocityField} (hC : ContDiff ℝ 1 u)
    (comp dir : Fin 3) : Continuous fun x => directionalCoord u comp dir x := by
  have hcoord : ContDiff ℝ 1 (fun y => u y comp) :=
    ((PiLp.proj (p := 2) (fun _ : Fin 3 => ℝ) comp : T3 →L[ℝ] ℝ)).contDiff.comp hC
  have hf : Continuous (fderiv ℝ (fun y => u y comp)) :=
    hcoord.continuous_fderiv (by simp)
  exact (hf.clm_apply continuous_const)

theorem continuous_vorticity_of_contDiff {u : VelocityField} (hC : ContDiff ℝ 1 u) :
    Continuous (vorticity u) := by
  have hc0 : Continuous fun x => curl u x 0 := by
    simpa [(curl_apply u _).1] using
      (continuous_directionalCoord hC 2 1).sub (continuous_directionalCoord hC 1 2)
  have hc1 : Continuous fun x => curl u x 1 := by
    simpa [(curl_apply u _).2.1] using
      (continuous_directionalCoord hC 0 2).sub (continuous_directionalCoord hC 2 0)
  have hc2 : Continuous fun x => curl u x 2 := by
    simpa [(curl_apply u _).2.2] using
      (continuous_directionalCoord hC 1 0).sub (continuous_directionalCoord hC 0 1)
  have hfun : vorticity u = fun y =>
      curl u y 0 • EuclideanSpace.single 0 (1 : ℝ) +
        curl u y 1 • EuclideanSpace.single 1 (1 : ℝ) +
        curl u y 2 • EuclideanSpace.single 2 (1 : ℝ) := by
    funext y
    ext i
    fin_cases i <;> simp [vorticity, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
  rw [hfun]
  exact ((hc0.smul continuous_const).add (hc1.smul continuous_const)).add
    (hc2.smul continuous_const)

theorem continuous_norm_vorticity_of_contDiff {u : VelocityField} (hC : ContDiff ℝ 1 u) :
    Continuous fun y => ‖vorticity u y‖ :=
  (continuous_vorticity_of_contDiff hC).norm

/-- Under `FeffermanDecay`, `|ω(x)| → 0` as `|x| → ∞`. -/
theorem vorticity_tendsto_zero_of_feffermanDecay {u : VelocityField}
    (hC : ContDiff ℝ 1 u) (h : FeffermanDecay u) :
    Tendsto (fun y => ‖vorticity u y‖) (cocompact T3) (nhds (0 : ℝ)) := by
  obtain ⟨C, hCnonneg, hbound⟩ := fderiv_bound_of_feffermanDecay h (1 : ℝ)
  have hcurl : ∀ y, ‖vorticity u y‖ ≤ 6 * C * (1 + ‖y‖) ^ (-(1 : ℝ)) := fun y => by
    have hu : DifferentiableAt ℝ u y := (hC.differentiable (by simp)).differentiableAt
    have h1 := (norm_curl_le_six_fderiv u y hu).trans
      (mul_le_mul_of_nonneg_left (hbound y) (by norm_num : (0 : ℝ) ≤ 6))
    simpa [vorticity, mul_assoc] using h1
  have hlim : Tendsto (fun y : T3 => 6 * C * (1 + ‖y‖) ^ (-(1 : ℝ)))
      (cocompact T3) (nhds (0 : ℝ)) := by
    have hnorm : Tendsto (fun y : T3 => ‖y‖) (cocompact T3) atTop :=
      tendsto_norm_cocompact_atTop
    have hone : Tendsto (fun y : T3 => 1 + ‖y‖) (cocompact T3) atTop :=
      tendsto_atTop_add_const_left (cocompact T3) (1 : ℝ) hnorm
    have hpow : Tendsto (fun y : T3 => (1 + ‖y‖) ^ (-(1 : ℝ))) (cocompact T3) (nhds 0) := by
      have hinv : Tendsto (fun t : ℝ => t ^ (-(1 : ℝ))) atTop (nhds 0) := by
        simpa [Real.rpow_neg_one] using tendsto_inv_atTop_zero
      exact hinv.comp hone
    have hmul :
        Tendsto (fun y : T3 => (6 * C) * (1 + ‖y‖) ^ (-(1 : ℝ)))
          (cocompact T3) (nhds ((6 * C) * 0)) :=
      (tendsto_const_nhds (x := (6 : ℝ) * C)).mul hpow
    have hz : (6 * C : ℝ) * 0 = 0 := by simp
    exact hz ▸ hmul
  exact squeeze_zero (fun _ => norm_nonneg _) hcurl hlim

/-- A `C¹` snapshot with `FeffermanDecay` attains a global maximum of `|ω|`. -/
theorem exists_isMaxOn_vorticity_of_feffermanDecay {u : VelocityField}
    (hC : ContDiff ℝ 1 u) (h : FeffermanDecay u) :
    ∃ x : T3, IsMaxOn (fun y => ‖vorticity u y‖) Set.univ x :=
  exists_isMaxOn_norm_vorticity_of_tendsto_zero
    (continuous_norm_vorticity_of_contDiff hC)
    (vorticity_tendsto_zero_of_feffermanDecay hC h)

/-! ## 3. `VorticityMaximumAttained` under snapshot decay, and the Fefferman slice -/

/-- Joint Fefferman smoothness implies every snapshot `u(t)` is `C^∞` in space. -/
theorem fefferman_snapshot_contDiff
    {ν T : ℝ} {u₀ : VelocityField} {u : TimeDependentVelocity} {p : TimeDependentPressure}
    (hu : IsFeffermanSolutionOn ν T u₀ u p)
    {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) T) :
    ContDiff ℝ ∞ (u t) := by
  have hmaps : Set.MapsTo (fun x : T3 => (x, t)) Set.univ
      (Set.univ ×ˢ Set.Ico (0 : ℝ) T) := fun _ _ => ⟨Set.mem_univ _, ht⟩
  have hpath : ContDiff ℝ ∞ (fun x : T3 => (x, t)) := contDiff_id.prodMk contDiff_const
  have := hu.1.comp hpath.contDiffOn hmaps
  simpa [contDiffOn_univ] using this

/-- A (possibly non-measurable) maximizing trajectory exists as soon as every snapshot
on `[0, T)` has continuous vorticity vanishing at infinity. This is exactly
`VorticityMaximumAttained`, under that extra hypothesis. -/
theorem exists_vorticityMaximumAttained_of_tendsto_zero
    (u : TimeDependentVelocity) (T : ℝ)
    (hc : ∀ t ∈ Set.Ico (0 : ℝ) T, Continuous fun y => ‖vorticity (u t) y‖)
    (h0 : ∀ t ∈ Set.Ico (0 : ℝ) T,
      Tendsto (fun y => ‖vorticity (u t) y‖) (cocompact T3) (nhds (0 : ℝ))) :
    ∃ x_max : ℝ → T3, VorticityMaximumAttained u T x_max := by
  choose x hx using fun t (ht : t ∈ Set.Ico (0 : ℝ) T) =>
    exists_isMaxOn_norm_vorticity_of_tendsto_zero (hc t ht) (h0 t ht)
  refine ⟨fun t => if ht : t ∈ Set.Ico (0 : ℝ) T then x t ht else 0, ?_⟩
  intro t ht
  simp [VorticityMaximumAttained, ht, hx t ht]

/-- The same conclusion, with the decay hypothesis written as `FeffermanDecay` of each
snapshot (which Fefferman (A) supplies for `u₀`, and which implies vanish-at-infinity). -/
theorem exists_vorticityMaximumAttained_of_snapshot_feffermanDecay
    {ν T : ℝ} {u₀ : VelocityField} {u : TimeDependentVelocity} {p : TimeDependentPressure}
    (hu : IsFeffermanSolutionOn ν T u₀ u p)
    (hdec : ∀ t ∈ Set.Ico (0 : ℝ) T, FeffermanDecay (u t)) :
    ∃ x_max : ℝ → T3, VorticityMaximumAttained u T x_max := by
  refine exists_vorticityMaximumAttained_of_tendsto_zero u T ?_ ?_
  · intro t ht
    exact continuous_norm_vorticity_of_contDiff
      ((fefferman_snapshot_contDiff hu ht).of_le (by simp))
  · intro t ht
    exact vorticity_tendsto_zero_of_feffermanDecay
      ((fefferman_snapshot_contDiff hu ht).of_le (by simp)) (hdec t ht)

/-- Fefferman (A) decay of the *initial* datum gives attainment at `t = 0` (provided
`0 < T`, so that `t = 0` lies in the existence interval). -/
theorem exists_isMaxOn_vorticity_at_zero
    {ν T : ℝ} {u₀ : VelocityField} {u : TimeDependentVelocity} {p : TimeDependentPressure}
    (hu : IsFeffermanSolutionOn ν T u₀ u p) (hT : 0 < T)
    (hdec : FeffermanDecay u₀) :
    ∃ x : T3, IsMaxOn (fun y => ‖vorticity (u 0) y‖) Set.univ x := by
  have ht : (0 : ℝ) ∈ Set.Ico (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hC : ContDiff ℝ 1 (u 0) := (fefferman_snapshot_contDiff hu ht).of_le (by simp)
  have hdec0 : FeffermanDecay (u 0) := by
    intro k α K
    simpa [funext hu.2.2.2.1] using hdec k α K
  exact exists_isMaxOn_vorticity_of_feffermanDecay hC hdec0

/-! ## 4. `IsFeffermanSolutionOn` alone does not imply attainment

The local solution class does not include spatial decay, finite energy, or `ν > 0`.
The stationary Euler shear `u = (y arctan y − ½ log(1+y²), 0, 0)` is a smooth
`IsFeffermanSolutionOn` solution (`ν = 0`) whose vorticity `(0,0,−arctan y)` never
attains its supremum `π/2`.
-/

/-- Antiderivative of `arctan`: `d/dy (y arctan y − ½ log(1+y²)) = arctan y`. -/
def arctanPotential (y : ℝ) : ℝ :=
  y * Real.arctan y - (1 / 2) * Real.log (1 + y ^ 2)


theorem hasDerivAt_arctanPotential (y : ℝ) :
    HasDerivAt arctanPotential (Real.arctan y) y := by
  have hmul : HasDerivAt (fun z => z * Real.arctan z)
      (1 * Real.arctan y + y * (1 / (1 + y ^ 2))) y :=
    (hasDerivAt_id y).mul (Real.hasDerivAt_arctan y)
  have hpos : 1 + y ^ 2 ≠ 0 := by nlinarith [sq_nonneg y]
  have hsq : HasDerivAt (fun z : ℝ => z ^ 2) (2 * y) y := by
    simpa using hasDerivAt_pow (n := 2) y
  have hinner := (hasDerivAt_const y (1 : ℝ)).add hsq
  have hlog := (Real.hasDerivAt_log (x := 1 + y ^ 2) hpos).comp y hinner
  have hhalf := hlog.const_mul (1 / 2 : ℝ)
  have hsub := hmul.sub hhalf
  convert hsub using 1
  have : (1 / 2 : ℝ) * ((1 + y ^ 2)⁻¹ * (2 * y)) = y * (1 / (1 + y ^ 2)) := by
    field
  simp [this]
  ring

theorem contDiff_arctanPotential : ContDiff ℝ ∞ arctanPotential := by
  have hmul : ContDiff ℝ ∞ (fun y => y * Real.arctan y) :=
    contDiff_id.mul Real.contDiff_arctan
  have hinner : ContDiff ℝ ∞ (fun y : ℝ => 1 + y ^ 2) :=
    contDiff_const.add ((contDiff_id (E := ℝ)).pow 2)
  have hlog : ContDiff ℝ ∞ (fun y => Real.log (1 + y ^ 2)) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    have hpt : ContDiffAt ℝ ∞ Real.log (1 + y ^ 2) :=
      (Real.contDiffAt_log).mpr (by nlinarith [sq_nonneg y])
    exact hpt.comp y hinner.contDiffAt
  have hhalf : ContDiff ℝ ∞ (fun y => (1 / 2 : ℝ) * Real.log (1 + y ^ 2)) :=
    contDiff_const.mul hlog
  exact hmul.sub hhalf

def arctanShearField : VelocityField :=
  fun x => EuclideanSpace.single 0 (arctanPotential (x 1))

def arctanShearFlow : TimeDependentVelocity := fun _ => arctanShearField

def arctanShearPressure : TimeDependentPressure := fun _ _ => 0

theorem contDiff_coord (i : Fin 3) : ContDiff ℝ ∞ (fun x : T3 => x i) :=
  ((PiLp.proj (p := 2) (fun _ : Fin 3 => ℝ) i : T3 →L[ℝ] ℝ)).contDiff

theorem arctanShearField_eq_smul :
    arctanShearField =
      fun x => arctanPotential (x 1) • EuclideanSpace.single 0 (1 : ℝ) := by
  funext x
  ext i
  simp [arctanShearField, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]

theorem contDiff_arctanShearField : ContDiff ℝ ∞ arctanShearField := by
  rw [arctanShearField_eq_smul]
  exact (contDiff_arctanPotential.comp (contDiff_coord 1)).smul contDiff_const

theorem differentiableAt_arctanShearField (x : T3) :
    DifferentiableAt ℝ arctanShearField x :=
  (contDiff_arctanShearField.differentiable (by simp)).differentiableAt

theorem fderiv_arctanPotential_coord (x : T3) (v : T3) :
    (fderiv ℝ (fun y : T3 => arctanPotential (y 1)) x) v =
      Real.arctan (x 1) * v 1 := by
  have hcoord : HasFDerivAt (fun y : T3 => y 1)
      ((PiLp.proj (p := 2) (fun _ : Fin 3 => ℝ) 1 : T3 →L[ℝ] ℝ)) x :=
    ((PiLp.proj (p := 2) (fun _ : Fin 3 => ℝ) 1 : T3 →L[ℝ] ℝ)).hasFDerivAt
  have hF := (hasDerivAt_arctanPotential (x 1)).comp_hasFDerivAt x hcoord
  have heq : (fun y : T3 => arctanPotential (y 1)) = arctanPotential ∘ fun y => y 1 := rfl
  rw [heq, hF.fderiv]
  simp [ContinuousLinearMap.smulRight_apply, smul_eq_mul]

theorem directionalCoord_arctanShear (comp dir : Fin 3) (x : T3) :
    directionalCoord arctanShearField comp dir x =
      if comp = 0 then Real.arctan (x 1) * (EuclideanSpace.single dir (1 : ℝ) 1)
      else 0 := by
  unfold directionalCoord
  by_cases hc : comp = 0
  · subst hc
    have hfun : (fun y => arctanShearField y 0) = fun y => arctanPotential (y 1) := by
      funext y
      simp [arctanShearField, PiLp.single_apply]
    rw [hfun, fderiv_arctanPotential_coord]
    simp
  · have hfun : (fun y => arctanShearField y comp) = fun _ => (0 : ℝ) := by
      funext y
      simp [arctanShearField, PiLp.single_apply, hc]
    rw [hfun, fderiv_fun_const]
    simp [hc]

theorem curl_arctanShearField (x : T3) :
    curl arctanShearField x = EuclideanSpace.single 2 (-Real.arctan (x 1)) := by
  ext i
  have h := curl_apply arctanShearField x
  fin_cases i <;> simp [h, directionalCoord_arctanShear, PiLp.single_apply]

theorem norm_vorticity_arctanShearField (x : T3) :
    ‖vorticity arctanShearField x‖ = |Real.arctan (x 1)| := by
  simp [vorticity, curl_arctanShearField, PiLp.norm_single, Real.norm_eq_abs]

theorem abs_arctan_eq_arctan_abs (t : ℝ) : |Real.arctan t| = Real.arctan |t| := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht, abs_of_nonneg (Real.arctan_nonneg.mpr ht)]
  · by_cases h0 : t = 0
    · subst t; simp
    · have ht' : t < 0 := lt_of_le_of_ne ht h0
      have htan : Real.arctan t < 0 := by
        have := Real.arctan_lt_arctan_iff.mpr ht'
        simpa [Real.arctan_zero] using this
      rw [abs_of_nonpos ht, abs_of_nonpos htan.le, Real.arctan_neg]

/-- `|arctan y|` does not attain a global maximum on `ℝ³`. -/
theorem not_isMaxOn_abs_arctan (x : T3) :
    ¬ IsMaxOn (fun y : T3 => ‖vorticity arctanShearField y‖) Set.univ x := by
  intro hmax
  let z : T3 := EuclideanSpace.single 1 (|x 1| + 1)
  have hz : ‖vorticity arctanShearField z‖ = Real.arctan (|x 1| + 1) := by
    rw [norm_vorticity_arctanShearField]
    have hpos : 0 ≤ |x 1| + 1 := by positivity
    have hz1 : z 1 = |x 1| + 1 := by simp [z, PiLp.single_apply]
    rw [hz1, abs_of_nonneg (Real.arctan_nonneg.mpr hpos)]
  have hx : ‖vorticity arctanShearField x‖ = |Real.arctan (x 1)| :=
    norm_vorticity_arctanShearField x
  have hlt : |Real.arctan (x 1)| < Real.arctan (|x 1| + 1) := by
    have hmono : Real.arctan |x 1| < Real.arctan (|x 1| + 1) :=
      Real.arctan_lt_arctan_iff.mpr (by linarith [abs_nonneg (x 1)])
    exact (abs_arctan_eq_arctan_abs (x 1)).symm ▸ hmono
  have : ‖vorticity arctanShearField z‖ ≤ ‖vorticity arctanShearField x‖ :=
    hmax (Set.mem_univ z)
  rw [hz, hx] at this
  linarith

theorem convective_arctanShearField (x : T3) :
    convective arctanShearField arctanShearField x = 0 := by
  unfold convective
  have hdir :
      (fderiv ℝ arctanShearField x) (EuclideanSpace.single 0 (1 : ℝ)) = 0 := by
    ext i
    have hproj :
        (fderiv ℝ arctanShearField x) (EuclideanSpace.single 0 (1 : ℝ)) i =
          (fderiv ℝ (fun y => arctanShearField y i) x)
            (EuclideanSpace.single 0 (1 : ℝ)) :=
      (fderiv_coord_apply arctanShearField x i (EuclideanSpace.single 0 (1 : ℝ))
        (differentiableAt_arctanShearField x)).symm
    have hdir' := directionalCoord_arctanShear i 0 x
    have : (fderiv ℝ (fun y => arctanShearField y i) x)
        (EuclideanSpace.single 0 (1 : ℝ)) = 0 := by
      simpa [directionalCoord, PiLp.single_apply] using hdir'
    rw [hproj, this]
    simp
  have hu : arctanShearField x =
      arctanPotential (x 1) • EuclideanSpace.single 0 (1 : ℝ) := by
    simp [arctanShearField_eq_smul]
  rw [hu, map_smul, hdir, smul_zero]

theorem div_arctanShearField (x : T3) : div arctanShearField x = 0 := by
  unfold div
  apply Finset.sum_eq_zero
  intro i _
  have h := directionalCoord_arctanShear i i x
  fin_cases i <;> simp [directionalCoord, PiLp.single_apply] at h ⊢ <;> exact h

theorem pressureGradient_zero (x : T3) :
    pressureGradient (fun _ => (0 : ℝ)) x = 0 := by
  unfold pressureGradient
  apply ext_inner_right (𝕜 := ℝ)
  intro v
  have hdiff : DifferentiableAt ℝ (fun _ : T3 => (0 : ℝ)) x := differentiableAt_const 0
  have h := inner_gradient_left (f := fun _ : T3 => (0 : ℝ)) (x := x) (y := v) hdiff
  have hf : fderiv ℝ (fun _ : T3 => (0 : ℝ)) x = 0 := by
    simp [fderiv_fun_const]
  simpa [hf, real_inner_comm] using h

theorem isFeffermanSolutionOn_arctanShear (T : ℝ) (hT : 0 < T) :
    IsFeffermanSolutionOn (0 : ℝ) T arctanShearField arctanShearFlow arctanShearPressure := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h : ContDiff ℝ ∞ (fun q : T3 × ℝ => arctanShearField q.1) :=
      contDiff_arctanShearField.comp contDiff_fst
    exact h.contDiffOn
  · exact contDiffOn_const
  · intro t ht x
    refine ⟨?_, ?_⟩
    · have hdt : derivWithin (fun s => arctanShearFlow s x) (Set.Ici (0 : ℝ)) t = 0 := by
        have hfun : (fun s => arctanShearFlow s x) = fun _ => arctanShearField x := rfl
        simp [hfun, derivWithin_const]
      have hu : arctanShearFlow t = arctanShearField := rfl
      have hp : arctanShearPressure t = fun _ => (0 : ℝ) := rfl
      rw [hdt, hu, hp]
      simp [convective_arctanShearField, pressureGradient_zero]
    · simpa [arctanShearFlow] using div_arctanShearField x
  · intro x; rfl
  · intro t ht
    exact le_rfl

/-- Kernel-checked disproof: `IsFeffermanSolutionOn` does not imply existence of a
maximizing trajectory. The shear is a genuine local Fefferman-class solution as the
class is written (`ν = 0`, energy integrals may both be infinite, no spatial decay). -/
theorem not_isFeffermanSolutionOn_implies_vorticityMaximumAttained :
    ¬ (∀ (ν T : ℝ) (u₀ : VelocityField) (u : TimeDependentVelocity)
        (p : TimeDependentPressure),
        IsFeffermanSolutionOn ν T u₀ u p →
          ∃ x_max : ℝ → T3, VorticityMaximumAttained u T x_max) := by
  intro h
  obtain ⟨x_max, hx⟩ :=
    h 0 1 arctanShearField arctanShearFlow arctanShearPressure
      (isFeffermanSolutionOn_arctanShear 1 (by norm_num))
  have ht : (0 : ℝ) ∈ Set.Ico (0 : ℝ) (1 : ℝ) := ⟨le_rfl, by norm_num⟩
  exact not_isMaxOn_abs_arctan (x_max 0) (hx 0 ht)

/-! ## 5. Lipschitz regularity of `M` and almost-everywhere differentiability -/

/-- Uniform-in-space bound on the time derivative of vorticity, on a time set `I`.
This is *not* implied by `IsFeffermanSolutionOn` (joint `C^∞` on `ℝ³ × [0,T)` does
not give bounds uniform in `x`). -/
def VorticityTimeDerivBddOn (u : TimeDependentVelocity) (I : Set ℝ) (C : ℝ) : Prop :=
  0 ≤ C ∧
    ∀ t ∈ I, ∀ x : T3,
      DifferentiableAt ℝ (fun s => vorticity (u s) x) t ∧
        ‖time_deriv (fun s => vorticity (u s)) t x‖ ≤ C

theorem abs_Mω_sub_le_of_timeDerivBdd
    {u : TimeDependentVelocity} {a b C : ℝ} {s t : ℝ}
    (hI : VorticityTimeDerivBddOn u (Set.Icc a b) C)
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b)
    (hbs : BddAbove (Set.range fun x => ‖vorticity (u s) x‖))
    (hbt : BddAbove (Set.range fun x => ‖vorticity (u t) x‖)) :
    |Mω u t - Mω u s| ≤ C * |t - s| := by
  have hpt (x : T3) :
      ‖vorticity (u t) x - vorticity (u s) x‖ ≤ C * |t - s| := by
    have hsI : Convex ℝ (Set.Icc a b) := convex_Icc a b
    have hdiff : ∀ τ ∈ Set.Icc a b,
        DifferentiableAt ℝ (fun ρ => vorticity (u ρ) x) τ :=
      fun τ hτ => (hI.2 τ hτ x).1
    have hbound : ∀ τ ∈ Set.Icc a b,
        ‖deriv (fun ρ => vorticity (u ρ) x) τ‖ ≤ C :=
      fun τ hτ => (hI.2 τ hτ x).2
    have := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound hsI hs ht
    simpa [Real.norm_eq_abs] using this
  have hle1 : Mω u t ≤ Mω u s + C * |t - s| := by
    refine ciSup_le fun x => ?_
    have htri : ‖vorticity (u t) x‖ ≤
        ‖vorticity (u t) x - vorticity (u s) x‖ + ‖vorticity (u s) x‖ := by
      simpa [sub_add_cancel] using
        (norm_add_le (vorticity (u t) x - vorticity (u s) x) (vorticity (u s) x))
    have hx : ‖vorticity (u s) x‖ ≤ Mω u s := le_vorticity_sup_norm _ x hbs
    linarith [htri, hpt x]
  have hle2 : Mω u s ≤ Mω u t + C * |t - s| := by
    refine ciSup_le fun x => ?_
    have htri : ‖vorticity (u s) x‖ ≤
        ‖vorticity (u s) x - vorticity (u t) x‖ + ‖vorticity (u t) x‖ := by
      simpa [sub_add_cancel] using
        (norm_add_le (vorticity (u s) x - vorticity (u t) x) (vorticity (u t) x))
    have hx : ‖vorticity (u t) x‖ ≤ Mω u t := le_vorticity_sup_norm _ x hbt
    have hpt' : ‖vorticity (u s) x - vorticity (u t) x‖ ≤ C * |t - s| := by
      simpa [norm_sub_rev] using hpt x
    linarith [htri, hpt', hx]
  rw [abs_sub_le_iff]
  constructor <;> linarith

theorem lipschitzOnWith_Mω_of_timeDerivBdd
    {u : TimeDependentVelocity} {a b C : ℝ}
    (hI : VorticityTimeDerivBddOn u (Set.Icc a b) C)
    (hbdd : ∀ τ ∈ Set.Icc a b, BddAbove (Set.range fun x => ‖vorticity (u τ) x‖)) :
    LipschitzOnWith ⟨C, hI.1⟩ (Mω u) (Set.Icc a b) := by
  refine (lipschitzOnWith_iff_dist_le_mul).2 ?_
  intro s hs t ht
  have := abs_Mω_sub_le_of_timeDerivBdd hI hs ht (hbdd s hs) (hbdd t ht)
  simpa [Real.dist_eq, NNReal.coe_mk, abs_sub_comm] using this

/-- On a compact time interval where `∂t ω` is uniformly bounded and `|ω|` is
bounded, `M` is differentiable almost everywhere (Rademacher). At interior points
this is two-sided differentiability. -/
theorem ae_differentiableAt_Mω_of_timeDerivBdd
    {u : TimeDependentVelocity} {a b C : ℝ}
    (hI : VorticityTimeDerivBddOn u (Set.Icc a b) C)
    (hbdd : ∀ τ ∈ Set.Icc a b, BddAbove (Set.range fun x => ‖vorticity (u τ) x‖))
    (hab : a < b) :
    ∀ᵐ t, t ∈ Set.Ioo a b → DifferentiableAt ℝ (Mω u) t := by
  have hlip := lipschitzOnWith_Mω_of_timeDerivBdd hI hbdd
  filter_upwards [hlip.ae_differentiableWithinAt_of_mem
    (μ := MeasureTheory.volume)] with t ht htIoo
  have htIcc : t ∈ Set.Icc a b := Set.Ioo_subset_Icc_self htIoo
  have hnhds : Set.Icc a b ∈ nhds t := Icc_mem_nhds htIoo.1 htIoo.2
  exact (ht htIcc).differentiableAt hnhds

/-- `BddAbove` of each snapshot follows from `VorticityMaximumAttained`. -/
theorem bddAbove_of_vorticityMaximumAttained
    {u : TimeDependentVelocity} {T : ℝ} {x_max : ℝ → T3}
    (hatt : VorticityMaximumAttained u T x_max) {t : ℝ}
    (ht : t ∈ Set.Ico (0 : ℝ) T) :
    BddAbove (Set.range fun y => ‖vorticity (u t) y‖) :=
  (isMaxOn_vorticity_sup_norm_eq (hatt t ht)).1

/-! ## 6. Danskin's identity at two-sided differentiability points -/

/-- If `M` is (two-sided) differentiable at a time `t` where a spatial maximum is
attained and `M(t) > 0`, and `|ω(s,x)| ≤ M(s)` for `s` near `t`, then
`M'(t) = ⟨ω, ∂t ω⟩ / M(t)` at that maximizer. This is equality, so in particular
`DanskinRateAt` holds. -/
theorem danskin_eq_of_differentiable
    (u : TimeDependentVelocity) (t : ℝ) (x : T3)
    (hM : DifferentiableAt ℝ (Mω u) t)
    (hω : DifferentiableAt ℝ (fun s => vorticity (u s) x) t)
    (hpos : 0 < Mω u t)
    (hmax : IsMaxOn (fun y => ‖vorticity (u t) y‖) Set.univ x)
    (hnear : ∀ᶠ s in nhds t, ‖vorticity (u s) x‖ ≤ Mω u s) :
    deriv (Mω u) t =
      inner ℝ (vorticity (u t) x)
        (time_deriv (fun s => vorticity (u s)) t x) / Mω u t := by
  have hMval : Mω u t = ‖vorticity (u t) x‖ :=
    (isMaxOn_vorticity_sup_norm_eq hmax).2
  have hwne : vorticity (u t) x ≠ 0 :=
    norm_pos_iff.mp (hMval ▸ hpos)
  have hnorm :=
    hasDerivAt_norm_of_ne_zero (fun s => vorticity (u s) x) t hω hwne
  have hnonneg : ∀ᶠ s in nhds t, 0 ≤ Mω u s - ‖vorticity (u s) x‖ := by
    filter_upwards [hnear] with s hs
    linarith
  have hzero : Mω u t - ‖vorticity (u t) x‖ = 0 := by
    rw [hMval, sub_self]
  have hmin : IsLocalMin (fun s => Mω u s - ‖vorticity (u s) x‖) t := by
    filter_upwards [hnonneg] with s hs
    simpa [hzero] using hs
  have hder0 : deriv (fun s => Mω u s - ‖vorticity (u s) x‖) t = 0 :=
    hmin.deriv_eq_zero
  have hsub :
      deriv (fun s => Mω u s - ‖vorticity (u s) x‖) t =
        deriv (Mω u) t - deriv (fun s => ‖vorticity (u s) x‖) t :=
    deriv_fun_sub hM hnorm.differentiableAt
  have hnormd :
      deriv (fun s => ‖vorticity (u s) x‖) t =
        inner ℝ (vorticity (u t) x)
          (deriv (fun s => vorticity (u s) x) t) / ‖vorticity (u t) x‖ :=
    hnorm.deriv
  have hzero' : deriv (Mω u) t - deriv (fun s => ‖vorticity (u s) x‖) t = 0 := by
    rw [← hsub, hder0]
  have hident :
      deriv (Mω u) t -
        inner ℝ (vorticity (u t) x)
          (time_deriv (fun s => vorticity (u s)) t x) / Mω u t = 0 := by
    change deriv (Mω u) t -
        inner ℝ (vorticity (u t) x)
          (deriv (fun s => vorticity (u s) x) t) / Mω u t = 0
    rw [hMval, ← hnormd]
    exact hzero'
  linarith

/-- Under `VorticityMaximumAttained` on `[0, T)`, the near-time comparison
`|ω(s,x)| ≤ M(s)` holds for `s` near an interior time `t`. -/
theorem eventually_norm_le_Mω_of_attained
    {u : TimeDependentVelocity} {T : ℝ} {x_max : ℝ → T3}
    (hatt : VorticityMaximumAttained u T x_max)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : T3) :
    ∀ᶠ s in nhds t, ‖vorticity (u s) x‖ ≤ Mω u s := by
  have hmem : Set.Ico (0 : ℝ) T ∈ nhds t := Ico_mem_nhds_of_mem_Ioo ht
  filter_upwards [hmem] with s hs
  have hmax := hatt s hs
  have heq := isMaxOn_vorticity_sup_norm_eq hmax
  exact (hmax (Set.mem_univ x)).trans_eq heq.2.symm

/-- Interior form of `DanskinRateAt` at a two-sided differentiability point, for
every maximizer (in particular, for `x_max t`). -/
theorem danskinRateAt_of_differentiable
    {u : TimeDependentVelocity} {T : ℝ} {x_max : ℝ → T3}
    (hatt : VorticityMaximumAttained u T x_max)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hM : DifferentiableAt ℝ (Mω u) t)
    (hω : DifferentiableAt ℝ (fun s => vorticity (u s) (x_max t)) t) :
    DanskinRateAt u t (x_max t) (deriv (Mω u) t) := by
  intro hpos
  have heq := danskin_eq_of_differentiable u t (x_max t) hM hω hpos
    (hatt t ⟨ht.1.le, ht.2⟩) (eventually_norm_le_Mω_of_attained hatt ht (x_max t))
  exact heq.le

/-- Almost-everywhere `DanskinRateAt` on a compact interior interval, under a
uniform time-derivative bound (which gives Lipschitz of `M` and a.e.
two-sided differentiability) together with attainment and differentiability of
`s ↦ ω(s, x_max t)` at each interior time (the latter follows from joint
Fefferman smoothness on `(0, T)`, and is kept as a hypothesis here). -/
theorem ae_danskinRateAt_of_timeDerivBdd
    {u : TimeDependentVelocity} {T a b C : ℝ} {x_max : ℝ → T3}
    (hatt : VorticityMaximumAttained u T x_max)
    (hI : VorticityTimeDerivBddOn u (Set.Icc a b) C)
    (hab : a < b) (ha : 0 < a) (hb : b < T)
    (hω : ∀ t ∈ Set.Ioo a b,
      DifferentiableAt ℝ (fun s => vorticity (u s) (x_max t)) t) :
    ∀ᵐ t, t ∈ Set.Ioo a b → DanskinRateAt u t (x_max t) (deriv (Mω u) t) := by
  have hbdd : ∀ τ ∈ Set.Icc a b, BddAbove (Set.range fun x => ‖vorticity (u τ) x‖) := by
    intro τ hτ
    have hτ' : τ ∈ Set.Ico (0 : ℝ) T :=
      ⟨le_trans ha.le hτ.1, lt_of_le_of_lt hτ.2 hb⟩
    exact bddAbove_of_vorticityMaximumAttained hatt hτ'
  filter_upwards [ae_differentiableAt_Mω_of_timeDerivBdd hI hbdd hab] with t hdiff htIoo
  have ht : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans ha htIoo.1, lt_trans htIoo.2 hb⟩
  exact danskinRateAt_of_differentiable hatt ht (hdiff htIoo) (hω t htIoo)

end VorticityMaxAttained

#print axioms VorticityMaxAttained.exists_isMaxOn_of_tendsto_zero
#print axioms VorticityMaxAttained.vorticity_tendsto_zero_of_feffermanDecay
#print axioms VorticityMaxAttained.exists_vorticityMaximumAttained_of_tendsto_zero
#print axioms VorticityMaxAttained.exists_vorticityMaximumAttained_of_snapshot_feffermanDecay
#print axioms VorticityMaxAttained.exists_isMaxOn_vorticity_at_zero
#print axioms VorticityMaxAttained.not_isFeffermanSolutionOn_implies_vorticityMaximumAttained
#print axioms VorticityMaxAttained.lipschitzOnWith_Mω_of_timeDerivBdd
#print axioms VorticityMaxAttained.ae_differentiableAt_Mω_of_timeDerivBdd
#print axioms VorticityMaxAttained.danskin_eq_of_differentiable
#print axioms VorticityMaxAttained.danskinRateAt_of_differentiable
#print axioms VorticityMaxAttained.ae_danskinRateAt_of_timeDerivBdd
