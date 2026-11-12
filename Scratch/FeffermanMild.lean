import Scratch.PersistenceHm
import Scratch.FeffermanSchwartz
import Scratch.FeffermanSobolev
import Scratch.InverseSobolev
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-! # From persisted mild solutions of Fefferman data to `IsFeffermanSolutionOn`

For Fefferman initial data (`C^∞`, divergence-free, `FeffermanDecay`) and `ν > 0`,
the `Ĥ^{k+1}` mild solution on the `Ĥ³` local time is realized as a physical field
via inverse Fourier transform. This file develops that realization and the upgrade
to `IsFeffermanSolutionOn` on `[0, T)`, then the maximal interval and the `H³`
blow-up alternative. The Kato–Ponce right-derivative bound is not proved here; it
appears as a named hypothesis in the assembly of `KatoMaximalSolution`. -/

open MeasureTheory FourierTransform Real Filter Topology Set Metric
open scoped ENNReal ContDiff InnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
namespace FeffermanMild

open LerayHeat SobolevFourier SobolevHilbert HeatSobolev Duhamel DuhamelUp
open ProductHm InverseSobolev FeffermanSchwartz FeffermanSobolev
open MildExistence PersistenceHm
open NavierStokes3D (VelocityField T3 TimeDependentVelocity TimeDependentPressure
  PressureField div convective pressureGradient laplacian)
open RepairedTether (FeffermanDecay IsFeffermanSolutionOn)

/-! ## Realification and the physical field of an `Ĥ^m` representative -/

/-- Coordinatewise real part `ℂ³ → ℝ³`. -/
def realify (v : V) : E3 := WithLp.toLp 2 (fun i => (v i).re)

lemma realify_cplx (y : E3) : realify (cplx y) = y := by
  ext i
  simp [realify, cplx_apply]

lemma cplx_realify_of_real {v : V} (hv : ∀ i, (v i).im = 0) :
    cplx (realify v) = v := by
  ext i
  apply Complex.ext
  · simp [realify, cplx_apply]
  · simp [realify, cplx_apply, hv i]

/-- Physical velocity obtained by inverse-Fourier of an `Ĥ^m` (Fourier-side) representative,
followed by taking real parts. -/
def physicalOfHm {m : ℕ} (G : Hm m) : VelocityField :=
  fun x => realify (𝓕⁻ (G : E3 → V) x)

lemma coeFn_toHm {m : ℕ} {F : L2V} (h : fourierEnergy m F < ⊤) :
    (toHm F h : E3 → V) =ᵐ[μw m] ((𝓕 F : L2V) : E3 → V) :=
  MemLp.coeFn_toLp (memLp_fourier_of_energy h)

lemma coeFn_toHm_vol {m : ℕ} {F : L2V} (h : fourierEnergy m F < ⊤) :
    (toHm F h : E3 → V) =ᵐ[volume] ((𝓕 F : L2V) : E3 → V) :=
  (coeFn_toHm h).filter_mono (Measure.AbsolutelyContinuous.ae_le (ac_vol m))

lemma toL2_eq_toSchwartz_toLp {f : VelocityField} (hf : ContDiff ℝ ∞ f)
    (h : FeffermanDecay f) :
    toL2 f hf h = (toSchwartz f hf h).toLp 2 :=
  MemLp.toLp_congr (memLp_cplx_of_feffermanDecay hf h)
    ((toSchwartz f hf h).memLp 2) (Filter.Eventually.of_forall fun _ => rfl)

lemma coeFn_fourier_toL2 {f : VelocityField} (hf : ContDiff ℝ ∞ f)
    (h : FeffermanDecay f) :
    ((𝓕 (toL2 f hf h) : L2V) : E3 → V) =ᵐ[volume] 𝓕 (cplx ∘ f) := by
  rw [toL2_eq_toSchwartz_toLp hf h, SchwartzMap.toLp_fourier_eq]
  have hfun : (toSchwartz f hf h : E3 → V) = cplx ∘ f := rfl
  refine ((𝓕 (toSchwartz f hf h)).memLp 2).coeFn_toLp.trans ?_
  rw [SchwartzMap.fourier_coe (toSchwartz f hf h), hfun]

/-- The Fourier-side `Ĥ^m` representative of Fefferman data inverts to the data itself. -/
theorem physicalOfHm_toHmFeff {f : VelocityField} (hf : ContDiff ℝ ∞ f)
    (h : FeffermanDecay f) (m : ℕ) :
    physicalOfHm (toHmFeff f hf h m) = f := by
  funext x
  unfold physicalOfHm toHmFeff
  have hae : (toHm (toL2 f hf h) (fourierEnergy_lt_top_of_feffermanDecay hf h m) : E3 → V)
      =ᵐ[volume] 𝓕 (cplx ∘ f) :=
    (coeFn_toHm_vol _).trans (coeFn_fourier_toL2 hf h)
  have hinv : 𝓕⁻ (toHm (toL2 f hf h) (fourierEnergy_lt_top_of_feffermanDecay hf h m) : E3 → V)
      = 𝓕⁻ (𝓕 (cplx ∘ f)) :=
    funext fun y => fourierInv_congr_ae hae y
  rw [hinv, fourierInv_fourier_cplx_of_fefferman hf h, Function.comp_apply, realify_cplx]

/-! ## Inclusions of Fefferman data in `Ĥ^m` -/

lemma incl_toHm {m m' : ℕ} (hle : m' ≤ m) {F : L2V}
    (hm : fourierEnergy m F < ⊤) (hm' : fourierEnergy m' F < ⊤) :
    incl hle (toHm F hm) = toHm F hm' := by
  refine Lp.ext ?_
  filter_upwards [coeFn_incl hle (toHm F hm),
    (ac_ww m m').ae_le (coeFn_toHm hm), coeFn_toHm hm'] with ξ h1 h2 h3
  rw [h1, h2, h3]

lemma incl_toHmFeff {f : VelocityField} (hf : ContDiff ℝ ∞ f) (h : FeffermanDecay f)
    {m m' : ℕ} (hle : m' ≤ m) :
    incl hle (toHmFeff f hf h m) = toHmFeff f hf h m' :=
  incl_toHm hle _ _

lemma incl_toHmFeff_three {f : VelocityField} (hf : ContDiff ℝ ∞ f)
    (h : FeffermanDecay f) {k : ℕ} (hk : 2 ≤ k) :
    incl (three_le_succ hk) (toHmFeff f hf h (k + 1)) = toHmFeff f hf h 3 :=
  incl_toHmFeff hf h (three_le_succ hk)

/-- The `Ĥ^{k+1}` mild solution of Fefferman data persists on the `Ĥ³` local time,
which depends only on the `Ĥ³` representative of the datum (not on `k`). -/
theorem persist_fefferman {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀) (hdec : FeffermanDecay u₀)
    {ν : ℝ} (hν : 0 < ν) {k : ℕ} (hk : 2 ≤ k) :
    ∃ u : XTs k (localTime ν (toHmFeff u₀ hf hdec 3)),
      IsMildS hk (localTime_nonneg hν (toHmFeff u₀ hf hdec 3)) ν
        (toHmFeff u₀ hf hdec (k + 1)) u ∧
      IsMild (localTime_nonneg hν (toHmFeff u₀ hf hdec 3)) ν
        (toHmFeff u₀ hf hdec 3) (inclMap hk u) ∧
      inclMap hk u ∈
        closedBall (0 : XT (localTime ν (toHmFeff u₀ hf hdec 3)))
          (rad (toHmFeff u₀ hf hdec 3)) := by
  have hincl := incl_toHmFeff_three hf hdec hk
  have h := persist_on_H3_time hk hν (toHmFeff u₀ hf hdec (k + 1))
  exact hincl ▸ h

#print axioms FeffermanMild.realify_cplx
#print axioms FeffermanMild.physicalOfHm_toHmFeff
#print axioms FeffermanMild.incl_toHmFeff
#print axioms FeffermanMild.persist_fefferman

/-! ## Spatial regularity of the physical field -/

lemma realify_add (v w : V) : realify (v + w) = realify v + realify w := by
  ext i
  simp [realify, PiLp.add_apply]

lemma realify_smul (c : ℝ) (v : V) : realify (c • v) = c • realify v := by
  ext i
  have hL : realify (c • v) i = ((c • v) i).re := by simp [realify]
  have hR : (c • realify v) i = c * (v i).re := by
    simp [realify, PiLp.smul_apply, smul_eq_mul]
  rw [hL, hR]
  have hsm : (c • v) i = (c : ℂ) * v i := by
    simp [Complex.real_smul]
  rw [hsm, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

lemma norm_realify_le (v : V) : ‖realify v‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  have hre : ‖realify v i‖ = |(v i).re| := by
    simp [realify, Real.norm_eq_abs]
  rw [hre]
  exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm (v i)) 2

/-- Coordinatewise real part, as a continuous real-linear map. -/
def realifyCLM : V →L[ℝ] E3 :=
  LinearMap.mkContinuous
    { toFun := realify
      map_add' := realify_add
      map_smul' := realify_smul }
    1 fun v => by simpa using norm_realify_le v

lemma realifyCLM_apply (v : V) : realifyCLM v = realify v := rfl

lemma physicalOfHm_eq_comp {m : ℕ} (G : Hm m) :
    physicalOfHm G = realifyCLM ∘ 𝓕⁻ (G : E3 → V) := rfl

/-- If `G ∈ Ĥ^m` and `m ≥ n + 2`, the physical field of `G` is `C^n`. -/
theorem contDiff_physicalOfHm {m n : ℕ} (hm : n + 2 ≤ m) (G : Hm m) :
    ContDiff ℝ n (physicalOfHm G) := by
  rw [physicalOfHm_eq_comp]
  exact (realifyCLM.contDiff.of_le (by exact_mod_cast le_top)).comp
    (contDiff_fourierInv_of_Hm hm G)

/-- Inclusion does not change the physical field: the Fourier representatives
agree almost everywhere, so the inverse Fourier transforms agree pointwise. -/
theorem physicalOfHm_incl {m m' : ℕ} (hle : m' ≤ m) (G : Hm m) :
    physicalOfHm (incl hle G) = physicalOfHm G := by
  funext x
  unfold physicalOfHm
  rw [fourierInv_congr_ae (coeFn_incl_vol hle G) x]

lemma incl_injective {m m' : ℕ} (hle : m' ≤ m) :
    Function.Injective (incl hle) := by
  intro G H hGH
  refine Lp.ext ?_
  have hG := coeFn_incl hle G
  have hH := coeFn_incl hle H
  have heq : (incl hle G : E3 → V) =ᵐ[μw m'] (incl hle H : E3 → V) :=
    EventuallyEq.of_eq (congrArg (fun z : Hm m' => (z : E3 → V)) hGH)
  have h' : (G : E3 → V) =ᵐ[μw m'] (H : E3 → V) := hG.symm.trans (heq.trans hH)
  exact h'.filter_mono (Measure.AbsolutelyContinuous.ae_le (ac_ww m' m))

/-! ## The realized physical path on the `Ĥ³` local time -/

/-- The `Ĥ³` local existence time of Fefferman data. -/
def Tfeff {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀) (hdec : FeffermanDecay u₀)
    {ν : ℝ} (_hν : 0 < ν) : ℝ :=
  localTime ν (toHmFeff u₀ hf hdec 3)

lemma Tfeff_nonneg {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀)
    (hdec : FeffermanDecay u₀) {ν : ℝ} (hν : 0 < ν) :
    0 ≤ Tfeff hf hdec hν :=
  localTime_nonneg hν _

lemma Tfeff_visc {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀)
    (hdec : FeffermanDecay u₀) {ν : ℝ} (hν : 0 < ν) :
    Tfeff hf hdec hν + 2 * Real.sqrt (Tfeff hf hdec hν / ν) ≤
      delta (toHmFeff u₀ hf hdec 3) :=
  localTime_visc hν _

/-- A persisted `Ĥ^{k+1}` mild path of Fefferman data, on the `Ĥ³` local time. -/
def persistPath {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀)
    (hdec : FeffermanDecay u₀) {ν : ℝ} (hν : 0 < ν) {k : ℕ} (hk : 2 ≤ k) :
    XTs k (Tfeff hf hdec hν) :=
  Classical.choose (persist_fefferman hf hdec hν hk)

lemma persistPath_spec {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀)
    (hdec : FeffermanDecay u₀) {ν : ℝ} (hν : 0 < ν) {k : ℕ} (hk : 2 ≤ k) :
    IsMildS hk (Tfeff_nonneg hf hdec hν) ν (toHmFeff u₀ hf hdec (k + 1))
      (persistPath hf hdec hν hk) ∧
    IsMild (Tfeff_nonneg hf hdec hν) ν (toHmFeff u₀ hf hdec 3)
      (inclMap hk (persistPath hf hdec hν hk)) ∧
    inclMap hk (persistPath hf hdec hν hk) ∈
      closedBall (0 : XT (Tfeff hf hdec hν)) (rad (toHmFeff u₀ hf hdec 3)) :=
  Classical.choose_spec (persist_fefferman hf hdec hν hk)

lemma persistPath_mildS {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀)
    (hdec : FeffermanDecay u₀) {ν : ℝ} (hν : 0 < ν) {k : ℕ} (hk : 2 ≤ k) :
    IsMildS hk (Tfeff_nonneg hf hdec hν) ν (toHmFeff u₀ hf hdec (k + 1))
      (persistPath hf hdec hν hk) :=
  (persistPath_spec hf hdec hν hk).1

lemma persistPath_mild3 {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀)
    (hdec : FeffermanDecay u₀) {ν : ℝ} (hν : 0 < ν) {k : ℕ} (hk : 2 ≤ k) :
    IsMild (Tfeff_nonneg hf hdec hν) ν (toHmFeff u₀ hf hdec 3)
      (inclMap hk (persistPath hf hdec hν hk)) :=
  (persistPath_spec hf hdec hν hk).2.1

lemma persistPath_memBall {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀)
    (hdec : FeffermanDecay u₀) {ν : ℝ} (hν : 0 < ν) {k : ℕ} (hk : 2 ≤ k) :
    inclMap hk (persistPath hf hdec hν hk) ∈
      closedBall (0 : XT (Tfeff hf hdec hν)) (rad (toHmFeff u₀ hf hdec 3)) :=
  (persistPath_spec hf hdec hν hk).2.2

/-- The `Ĥ³` shadows of the persisted paths (any `k`) agree, by uniqueness
of the mild solution in the working ball. -/
theorem inclMap_persistPath_unique {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀)
    (hdec : FeffermanDecay u₀) {ν : ℝ} (hν : 0 < ν)
    {k k' : ℕ} (hk : 2 ≤ k) (hk' : 2 ≤ k') :
    inclMap hk (persistPath hf hdec hν hk) =
      inclMap hk' (persistPath hf hdec hν hk') :=
  unique_mild_in_ball hν (Tfeff_nonneg hf hdec hν) (toHmFeff u₀ hf hdec 3)
    (Tfeff_visc hf hdec hν)
    (persistPath_memBall hf hdec hν hk) (persistPath_memBall hf hdec hν hk')
    (persistPath_mild3 hf hdec hν hk) (persistPath_mild3 hf hdec hν hk')

/-- The physical field of a persisted path is independent of the Sobolev index. -/
theorem physicalOfHm_persistPath_eq {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀)
    (hdec : FeffermanDecay u₀) {ν : ℝ} (hν : 0 < ν)
    {k k' : ℕ} (hk : 2 ≤ k) (hk' : 2 ≤ k')
    (t : Icc (0 : ℝ) (Tfeff hf hdec hν)) :
    physicalOfHm (persistPath hf hdec hν hk t) =
      physicalOfHm (persistPath hf hdec hν hk' t) := by
  have h3 :
      incl (three_le_succ hk) (persistPath hf hdec hν hk t) =
        incl (three_le_succ hk') (persistPath hf hdec hν hk' t) :=
    congrArg (fun u : XT (Tfeff hf hdec hν) => u t)
      (inclMap_persistPath_unique hf hdec hν hk hk')
  rw [← physicalOfHm_incl (three_le_succ hk),
    ← physicalOfHm_incl (three_le_succ hk'), h3]

/-- Physical velocity realized from the persisted mild solution.
Outside `[0, T]` the path is extended by the endpoint values of the
continuous `Ĥ³` representative (the Fefferman-class statement only
constrains `[0, T)`). -/
def physicalMild {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀)
    (hdec : FeffermanDecay u₀) {ν : ℝ} (hν : 0 < ν) :
    TimeDependentVelocity :=
  fun t => physicalOfHm
    (ContinuousMap.IccExtend (Tfeff_nonneg hf hdec hν)
      (persistPath hf hdec hν (by norm_num : 2 ≤ 2)) t)

lemma physicalMild_apply {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀)
    (hdec : FeffermanDecay u₀) {ν : ℝ} (hν : 0 < ν)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (Tfeff hf hdec hν)) :
    physicalMild hf hdec hν t =
      physicalOfHm (persistPath hf hdec hν (by norm_num : 2 ≤ 2) ⟨t, ht⟩) := by
  unfold physicalMild
  refine congrArg physicalOfHm ?_
  rw [ContinuousMap.coe_IccExtend]
  exact Set.IccExtend_of_mem
    (h := Tfeff_nonneg hf hdec hν)
    (persistPath hf hdec hν (by norm_num : 2 ≤ 2)) ht

lemma physicalMild_eq_path {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀)
    (hdec : FeffermanDecay u₀) {ν : ℝ} (hν : 0 < ν)
    {k : ℕ} (hk : 2 ≤ k)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (Tfeff hf hdec hν)) :
    physicalMild hf hdec hν t =
      physicalOfHm (persistPath hf hdec hν hk ⟨t, ht⟩) :=
  (physicalMild_apply hf hdec hν ht).trans
    (physicalOfHm_persistPath_eq hf hdec hν (by norm_num : 2 ≤ 2) hk ⟨t, ht⟩)

/-- The realized path starts at the Fefferman datum. -/
theorem physicalMild_zero {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀)
    (hdec : FeffermanDecay u₀) {ν : ℝ} (hν : 0 < ν) :
    physicalMild hf hdec hν 0 = u₀ := by
  have hT := Tfeff_nonneg hf hdec hν
  have ht : (0 : ℝ) ∈ Icc 0 (Tfeff hf hdec hν) := ⟨le_rfl, hT⟩
  rw [physicalMild_apply hf hdec hν ht,
    isMildS_zero' (by norm_num : 2 ≤ 2) hT _
      (persistPath_mildS hf hdec hν (by norm_num : 2 ≤ 2)),
    physicalOfHm_toHmFeff hf hdec 3]

/-- At every time in the closed local interval the realized field is `C^∞`
in space (it agrees with the inverse Fourier transform of an `Ĥ^{k+1}`
representative for every `k`). -/
theorem contDiff_physicalMild {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀)
    (hdec : FeffermanDecay u₀) {ν : ℝ} (hν : 0 < ν)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (Tfeff hf hdec hν)) :
    ContDiff ℝ ∞ (physicalMild hf hdec hν t) := by
  rw [contDiff_infty]
  intro n
  let k := max 2 (n + 1)
  have hk : 2 ≤ k := le_max_left _ _
  have hmn : n + 2 ≤ k + 1 := by
    have : n + 1 ≤ k := le_max_right _ _
    omega
  rw [physicalMild_eq_path hf hdec hν hk ht]
  exact contDiff_physicalOfHm hmn _

#print axioms FeffermanMild.contDiff_physicalOfHm
#print axioms FeffermanMild.physicalOfHm_incl
#print axioms FeffermanMild.inclMap_persistPath_unique
#print axioms FeffermanMild.physicalMild_zero
#print axioms FeffermanMild.contDiff_physicalMild

end FeffermanMild
