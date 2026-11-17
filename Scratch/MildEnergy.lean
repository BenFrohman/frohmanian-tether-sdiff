/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import Scratch.PlancherelBridge
import Scratch.KatoPonce

/-!
 # The `H³` energy of the realized mild field

Word derivatives of the physical field of an `Ĥ^m` slice are physical
fields of the corresponding Fourier multipliers; with the Plancherel bridge
this identifies the physical `H³` pairing `∑_{|α|≤3} ∫ ⟨∂^α u, ∂^α v⟩` with
the real part of the `Ĥ³` inner product, and yields the right-derivative
formula for `‖u(t)‖²_{H³}` along the mild path.
-/

open MeasureTheory Real Filter Topology Set FourierTransform
open scoped ENNReal ContDiff

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
namespace MildEnergy

open LerayHeat SobolevFourier SobolevHilbert InverseSobolev LerayPressure FourierInvBCF
  FourierInvFDeriv NonlinearHm InclNSN PlancherelBridge MildMomentum FeffermanMild

/-! ## Plancherel for inner products -/

theorem integral_inner_fourierInvBCF {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (A : Hm m) (B : Hm n) :
    ∫ x, inner ℂ (fourierInvBCF hm A x) (fourierInvBCF hn B x) =
      ∫ ξ, inner ℂ ((A : E3 → V) ξ) ((B : E3 → V) ξ) := by
  have h := Lp.inner_fourier_eq (𝓕⁻ (toL2V A) : L2V) (𝓕⁻ (toL2V B) : L2V)
  rw [fourier_fourierInv_eq, fourier_fourierInv_eq, MeasureTheory.L2.inner_def,
    MeasureTheory.L2.inner_def] at h
  rw [integral_congr_ae (by
      filter_upwards [coeFn_fourierInv_toL2V hm A, coeFn_fourierInv_toL2V hn B] with x ha hb
      rw [← ha, ← hb])]
  refine h.symm.trans ?_
  exact integral_congr_ae (by
    filter_upwards [coeFn_toL2V A, coeFn_toL2V B] with x ha hb
    rw [ha, hb])

/-! ## Word derivatives of `fourierInvBCF` -/

lemma dw_succ' {g : E3 → V} {k : ℕ} (hg : ContDiff ℝ (k + 1) g) (α : Fin (k + 1) → Fin 3) :
    dw α g = fun x => fderiv ℝ (dw (Fin.tail α) g) x (EuclideanSpace.single (α 0) (1 : ℝ)) := by
  funext x
  simp only [dw]
  rw [iteratedFDeriv_succ_apply_left]
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k g) x :=
    (hg.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self k)) x
  show _ = fderiv ℝ (fun y => iteratedFDeriv ℝ k g y (U (Fin.tail α))) x _
  rw [fderiv_continuousMultilinear_apply_const_apply hd]
  rfl

/-- **Word derivatives on the Fourier side.** For `A ∈ Ĥ^m` and a word `α`
of length `k` with `k + 2 ≤ m`, `∂^α (fourierInvBCF A) = fourierInvBCF A'`
for some `A'` whose representative is `(∏ⱼ 2πi ξ_{αⱼ}) A`. -/
theorem dw_fourierInvBCF : ∀ (k : ℕ) {m : ℕ} (hm : k + 2 ≤ m) (A : Hm m) (α : Fin k → Fin 3),
    ∃ (n : ℕ) (hn : 2 ≤ n) (A' : Hm n), m ≤ n + k ∧
      ((A' : E3 → V) =ᵐ[volume] fun ξ => (∏ j, sym (α j) ξ) • (A : E3 → V) ξ) ∧
      dw α (fourierInvBCF (by omega) A : E3 → V) = (fourierInvBCF hn A' : E3 → V)
  | 0, m, hm, A, α => by
    refine ⟨m, hm, A, by omega, Eventually.of_forall fun ξ => by simp, ?_⟩
    rw [dw_zero]
  | k + 1, m, hm, A, α => by
    obtain ⟨n, hn, A'', hmn, hae, hdw⟩ := dw_fourierInvBCF k (by omega : k + 2 ≤ m) A (Fin.tail α)
    have hn3 : 3 ≤ n := by omega
    refine ⟨n - 1, by omega, dH (one_le_of_three hn3) (α 0) A'', by omega, ?_, ?_⟩
    · filter_upwards [(ac_vol (n - 1)).ae_le (coeFn_dH (one_le_of_three hn3) (α 0) A''), hae]
        with ξ h1 h2
      rw [h1, Nonlinear.derivSym_apply, h2, smul_smul, Fin.prod_univ_succ]
      rfl
    · have hg : ContDiff ℝ (k + 1) (fourierInvBCF (by omega : 2 ≤ m) A : E3 → V) :=
        contDiff_fourierInv_of_Hm (by omega) A
      rw [dw_succ' hg]
      funext x
      have hfun : dw (Fin.tail α) (fourierInvBCF (by omega : 2 ≤ m) A : E3 → V) =
          fun y => 𝓕⁻ (A'' : E3 → V) y := by
        rw [show (fourierInvBCF (by omega : 2 ≤ m) A : E3 → V) =
          (fourierInvBCF (by omega : 2 ≤ m) A : E3 → V) from rfl, hdw]
        rfl
      rw [hfun, fderiv_fourierInv_single hn3]
      rfl

lemma integrable_inner_fourierInvBCF {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (A : Hm m) (B : Hm n) :
    Integrable (fun x => inner ℂ (fourierInvBCF hm A x) (fourierInvBCF hn B x)) := by
  refine (L2.integrable_inner (𝕜 := ℂ) (𝓕⁻ (toL2V A) : L2V) (𝓕⁻ (toL2V B) : L2V)).congr ?_
  filter_upwards [coeFn_fourierInv_toL2V hm A, coeFn_fourierInv_toL2V hn B] with x ha hb
  rw [ha, hb]

lemma integrable_inner_Hm {m n : ℕ} (A : Hm m) (B : Hm n) :
    Integrable (fun ξ => inner ℂ ((A : E3 → V) ξ) ((B : E3 → V) ξ)) := by
  refine (L2.integrable_inner (𝕜 := ℂ) (toL2V A) (toL2V B)).congr ?_
  filter_upwards [coeFn_toL2V A, coeFn_toL2V B] with x ha hb
  rw [ha, hb]

/-! ## Physical word derivatives of a real slice -/

/-- A slice whose inverse Fourier transform is real-valued. -/
def IsRealSlice {m : ℕ} (hm : 2 ≤ m) (A : Hm m) : Prop :=
  ∀ y : E3, ∀ i : Fin 3, (fourierInvBCF hm A y i).im = 0

lemma fourierInvBCF_eq_cplx {m : ℕ} (hm : 2 ≤ m) {A : Hm m} (hA : IsRealSlice hm A) :
    (fourierInvBCF hm A : E3 → V) = SobolevFourier.cplx ∘ physicalOfHm A := by
  funext y
  exact (cplx_realify_of_real (hA y)).symm

lemma wordDeriv_physicalOfHm {m k : ℕ} (hm : k + 2 ≤ m) (A : Hm m) (α : Fin k → Fin 3)
    (x : E3) :
    KatoPonce.wordDeriv k α (physicalOfHm A) x =
      realify (dw α (fourierInvBCF (by omega) A : E3 → V) x) := by
  have hg : ContDiff ℝ k (𝓕⁻ (A : E3 → V)) := contDiff_fourierInv_of_Hm hm A
  unfold KatoPonce.wordDeriv
  rw [physicalOfHm_eq_comp, realifyCLM.iteratedFDeriv_comp_left hg.contDiffAt le_rfl]
  rfl

lemma dw_im_eq_zero {m k : ℕ} (hm : k + 2 ≤ m) {A : Hm m}
    (hA : IsRealSlice (by omega) A) (α : Fin k → Fin 3) (x : E3) (i : Fin 3) :
    (dw α (fourierInvBCF (by omega : 2 ≤ m) A : E3 → V) x i).im = 0 := by
  have hf : ContDiff ℝ k (physicalOfHm A) := contDiff_physicalOfHm hm A
  rw [fourierInvBCF_eq_cplx _ hA]
  simp only [dw]
  rw [SobolevFourier.cplx.iteratedFDeriv_comp_left hf.contDiffAt le_rfl]
  change (SobolevFourier.cplx _ i).im = 0
  rw [SobolevFourier.cplx_apply, Complex.ofReal_im]

lemma inner_realify_of_real {v w : V} (hv : ∀ i, (v i).im = 0) :
    inner ℝ (realify v) (realify w) = (inner ℂ v w).re := by
  simp only [realify, PiLp.inner_apply, Complex.re_sum, RCLike.inner_apply,
    Complex.mul_re, Complex.conj_re, Complex.conj_im, hv]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm]
  simp [mul_comm]
  rfl

/-- **One word.** For real slices `A, B ∈ Ĥ^m` and a word of length `k`, `k + 2 ≤ m`:
`∫ ⟨∂^α u_A, ∂^α u_B⟩ = Re ∫ ⟨(∏ 2πiξ_α) A, (∏ 2πiξ_α) B⟩`. -/
theorem integral_inner_wordDeriv {m k : ℕ} (hm : k + 2 ≤ m) {A B : Hm m}
    (hA : IsRealSlice (by omega) A) (α : Fin k → Fin 3) :
    ∫ x, inner ℝ (KatoPonce.wordDeriv k α (physicalOfHm A) x)
        (KatoPonce.wordDeriv k α (physicalOfHm B) x) =
      (∫ ξ, inner ℂ ((∏ j, sym (α j) ξ) • (A : E3 → V) ξ)
        ((∏ j, sym (α j) ξ) • (B : E3 → V) ξ)).re := by
  obtain ⟨n₁, hn₁, A', -, hA', hdA⟩ := dw_fourierInvBCF k hm A α
  obtain ⟨n₂, hn₂, B', -, hB', hdB⟩ := dw_fourierInvBCF k hm B α
  simp only [wordDeriv_physicalOfHm hm]
  have hpt : ∀ x, inner ℝ (realify (dw α (fourierInvBCF (by omega : 2 ≤ m) A : E3 → V) x))
      (realify (dw α (fourierInvBCF (by omega : 2 ≤ m) B : E3 → V) x)) =
      (inner ℂ (fourierInvBCF hn₁ A' x) (fourierInvBCF hn₂ B' x)).re := by
    intro x
    rw [inner_realify_of_real (dw_im_eq_zero hm hA α x), hdA, hdB]
  simp only [hpt]
  have hre := integral_re (𝕜 := ℂ) (integrable_inner_fourierInvBCF hn₁ hn₂ A' B')
  simp only [RCLike.re_to_complex] at hre
  rw [hre]
  congr 1
  refine (integral_inner_fourierInvBCF hn₁ hn₂ A' B').trans ?_
  exact integral_congr_ae (by filter_upwards [hA', hB'] with ξ h1 h2; rw [h1, h2])

/-! ## Summing over words: the `Ĥ³` inner product -/

lemma sobW_toReal (m : ℕ) (ξ : E3) :
    (sobW m ξ).toReal = ∑ k ∈ Finset.range (m + 1), ∑ α : Fin k → Fin 3,
      ‖∏ j, sym (α j) ξ‖ ^ 2 := by
  unfold sobW
  rw [ENNReal.toReal_sum (fun k _ => ENNReal.pow_ne_top (ENNReal.sum_ne_top.2 fun i _ =>
    ENNReal.pow_ne_top enorm_ne_top))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ENNReal.toReal_pow, ENNReal.toReal_sum (fun i _ => ENNReal.pow_ne_top enorm_ne_top)]
  simp only [ENNReal.toReal_pow, toReal_enorm, norm_prod, ← Finset.prod_pow]
  have := Finset.prod_univ_sum (fun _ : Fin k => (Finset.univ : Finset (Fin 3)))
    (fun _ i => ‖sym i ξ‖ ^ 2)
  rw [Fintype.piFinset_univ] at this
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
  exact this

lemma inner_smul_smul (c : ℂ) (a b : V) :
    inner ℂ (c • a) (c • b) = ((‖c‖ ^ 2 : ℝ) : ℂ) * inner ℂ a b := by
  rw [inner_smul_left, inner_smul_right, ← mul_assoc, Complex.conj_mul']
  push_cast; ring

lemma integrable_inner_word {m k : ℕ} (hm : k + 2 ≤ m) (A B : Hm m) (α : Fin k → Fin 3) :
    Integrable (fun ξ => inner ℂ ((∏ j, sym (α j) ξ) • (A : E3 → V) ξ)
      ((∏ j, sym (α j) ξ) • (B : E3 → V) ξ)) := by
  obtain ⟨n₁, -, A', -, hA', -⟩ := dw_fourierInvBCF k hm A α
  obtain ⟨n₂, -, B', -, hB', -⟩ := dw_fourierInvBCF k hm B α
  exact (integrable_inner_Hm A' B').congr (by filter_upwards [hA', hB'] with ξ h1 h2; rw [h1, h2])

/-- Real part of the `Ĥ³` inner product as an integral against the weight. -/
lemma inner_incl_three {m : ℕ} (h : 3 ≤ m) (A B : Hm m) :
    inner ℂ (incl h A) (incl h B) =
      ∫ ξ, (((sobW 3 ξ).toReal : ℝ) : ℂ) * inner ℂ ((A : E3 → V) ξ) ((B : E3 → V) ξ) := by
  rw [MeasureTheory.L2.inner_def]
  rw [integral_congr_ae (by
    filter_upwards [ProductHm.coeFn_incl h A, ProductHm.coeFn_incl h B] with ξ h1 h2
    rw [h1, h2])]
  rw [μw, integral_withDensity_eq_integral_toReal_smul (measurable_sobW 3)
    (Eventually.of_forall fun ξ => sobW_lt_top 3 ξ)]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [Complex.real_smul]

/-- **Physical `H³` pairing = `Re ⟨·,·⟩_{Ĥ³}`.** For real slices
`A, B ∈ Ĥ^m` (`m ≥ 5`, only `A` real is needed), the physical pairing
`∑_{|α|≤3} ∫ ⟨∂^α u_A, ∂^α u_B⟩` equals the real part of the `Ĥ³` inner
product of `A` and `B`. -/
theorem physical_pairing_eq {m : ℕ} (hm : 5 ≤ m) {A B : Hm m}
    (hA : IsRealSlice (by omega) A) :
    ∑ k ∈ Finset.range 4, ∑ α : Fin k → Fin 3,
      ∫ x, inner ℝ (KatoPonce.wordDeriv k α (physicalOfHm A) x)
        (KatoPonce.wordDeriv k α (physicalOfHm B) x) =
      (inner ℂ (incl (by omega : 3 ≤ m) A) (incl (by omega : 3 ≤ m) B)).re := by
  have hk : ∀ k ∈ Finset.range 4, k + 2 ≤ m := fun k hk' => by
    have := Finset.mem_range.1 hk'; omega
  rw [Finset.sum_congr rfl fun k hk' => Finset.sum_congr rfl fun α _ =>
    integral_inner_wordDeriv (hk k hk') (B := B) hA α]
  simp only [← Complex.re_sum]
  congr 1
  rw [Finset.sum_congr rfl fun k hk' => (integral_finset_sum _ fun α _ =>
    integrable_inner_word (hk k hk') A B α).symm]
  rw [← integral_finset_sum _ fun k hk' => integrable_finset_sum _ fun α _ =>
    integrable_inner_word (hk k hk') A B α]
  rw [inner_incl_three]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [inner_smul_smul, ← Finset.sum_mul, sobW_toReal]
  push_cast
  rfl

lemma integrable_inner_wordDeriv {m k : ℕ} (hm : k + 2 ≤ m) {A : Hm m}
    (hA : IsRealSlice (by omega) A) (B : Hm m) (α : Fin k → Fin 3) :
    Integrable (fun x => inner ℝ (KatoPonce.wordDeriv k α (physicalOfHm A) x)
        (KatoPonce.wordDeriv k α (physicalOfHm B) x)) := by
  obtain ⟨n₁, hn₁, A', -, -, hdA⟩ := dw_fourierInvBCF k hm A α
  obtain ⟨n₂, hn₂, B', -, -, hdB⟩ := dw_fourierInvBCF k hm B α
  have hpt : ∀ x, inner ℝ (KatoPonce.wordDeriv k α (physicalOfHm A) x)
      (KatoPonce.wordDeriv k α (physicalOfHm B) x) =
      Complex.reCLM (inner ℂ (fourierInvBCF hn₁ A' x) (fourierInvBCF hn₂ B' x)) := by
    intro x
    rw [wordDeriv_physicalOfHm hm, wordDeriv_physicalOfHm hm,
      inner_realify_of_real (dw_im_eq_zero hm hA α x), hdA, hdB]
    rfl
  simp only [hpt]
  exact Complex.reCLM.integrable_comp (integrable_inner_fourierInvBCF hn₁ hn₂ A' B')

lemma lintegral_enorm_sq_eq_ofReal {f : E3 → E3}
    (hf : Integrable fun x => inner ℝ (f x) (f x)) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 = ENNReal.ofReal (∫ x, inner ℝ (f x) (f x)) := by
  rw [ofReal_integral_eq_lintegral_ofReal hf
    (Eventually.of_forall fun x => real_inner_self_nonneg)]
  refine lintegral_congr fun x => ?_
  rw [real_inner_self_eq_norm_sq, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

/-- **`H³` energy of a real slice.** For a real slice `A ∈ Ĥ^m` (`m ≥ 5`),
the physical `H³` energy of `physicalOfHm A` is finite and equals `‖A‖²_{Ĥ³}`. -/
theorem sobolevEnergy_physicalOfHm {m : ℕ} (hm : 5 ≤ m) {A : Hm m}
    (hA : IsRealSlice (by omega) A) :
    R3BKM.sobolevEnergy 3 (physicalOfHm A) =
      ENNReal.ofReal (‖incl (by omega : 3 ≤ m) A‖ ^ 2) := by
  have hk : ∀ k ∈ Finset.range 4, k + 2 ≤ m := fun k hk' => by
    have := Finset.mem_range.1 hk'; omega
  unfold R3BKM.sobolevEnergy
  show ∑ k ∈ Finset.range 4, ∑ α : Fin k → Fin 3,
    ∫⁻ x, ‖KatoPonce.wordDeriv k α (physicalOfHm A) x‖ₑ ^ 2 = _
  rw [Finset.sum_congr rfl fun k hk' => Finset.sum_congr rfl fun α _ =>
    lintegral_enorm_sq_eq_ofReal (f := KatoPonce.wordDeriv k α (physicalOfHm A))
      (integrable_inner_wordDeriv (hk k hk') hA A α)]
  rw [Finset.sum_congr rfl fun k _ => (ENNReal.ofReal_sum_of_nonneg fun α _ =>
    integral_nonneg fun x => real_inner_self_nonneg).symm]
  rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => Finset.sum_nonneg fun α _ =>
    integral_nonneg fun x => real_inner_self_nonneg]
  congr 1
  refine (physical_pairing_eq hm (B := A) hA).trans ?_
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
  rfl

theorem hsSq_physicalOfHm {m : ℕ} (hm : 5 ≤ m) {A : Hm m}
    (hA : IsRealSlice (by omega) A) :
    R3BKM.hsSq 3 (physicalOfHm A) = ‖incl (by omega : 3 ≤ m) A‖ ^ 2 := by
  rw [R3BKM.hsSq, sobolevEnergy_physicalOfHm hm hA, ENNReal.toReal_ofReal (sq_nonneg _)]

/-! ## Item 4: the `H³` energy right-derivative formula along the mild path -/

open MildTimeDeriv MildPathSmooth RepairedTether NavierStokes3D HeatDeriv MildReal

/-- Inclusion as a real continuous linear map. -/
def inclR {m m' : ℕ} (h : m' ≤ m) : Hm m →L[ℝ] Hm m' :=
  (NonlinearSmooth.isBoundedLinearMap_restrictCLM (incl h : Hm m →L[ℂ] Hm m')
    (fun c x => NonlinearSmooth.real_smul_eq_coe_smul c x)
    (fun c y => NonlinearSmooth.real_smul_eq_coe_smul c y)).toContinuousLinearMap

lemma inclR_apply {m m' : ℕ} (h : m' ≤ m) (G : Hm m) : inclR h G = incl h G := rfl

section MildPath

variable {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀) (hdec : FeffermanDecay u₀)
  {ν : ℝ} (hν : 0 < ν)

/-- The persisted path of index `k`, included into `Ĥ^m` and extended to `ℝ`. -/
abbrev pathExt {k : ℕ} (hk : 2 ≤ k) {m : ℕ} (hle : m ≤ k + 1) : ℝ → Hm m :=
  inclExt hle (Tfeff_nonneg hf hdec hν) (persistPath hf hdec hν hk)

lemma hasDerivWithinAt_pathExt {k : ℕ} (hk : 2 ≤ k) {m : ℕ} (hm2 : m + 2 ≤ k)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) (Tfeff hf hdec hν)) :
    HasDerivWithinAt (pathExt hf hdec hν hk (le_succ_of_add_two_le hm2))
      (mildSDeriv hk hm2 hν (Tfeff_nonneg hf hdec hν)
        (FeffermanSobolev.toHmFeff u₀ hf hdec (k + 1)) (persistPath hf hdec hν hk) t)
      (Ico 0 (Tfeff hf hdec hν)) t :=
  hasDerivWithinAt_mildS_incl_Ico hk hm2 hν (Tfeff_nonneg hf hdec hν)
    (persistPath_mildS hf hdec hν hk) ht

lemma refl_pathExt {k : ℕ} (hk : 2 ≤ k) {m : ℕ} (hle : m ≤ k + 1) (t : ℝ) :
    refl m (pathExt hf hdec hν hk hle t) = pathExt hf hdec hν hk hle t := by
  simp only [pathExt, inclExt]
  rw [refl_incl, IccExtend_persistPath_apply, refl_persistPath_high]

lemma isRealSlice_pathExt {k : ℕ} (hk : 2 ≤ k) {m : ℕ} (hm : 2 ≤ m) (hle : m ≤ k + 1)
    (t : ℝ) : IsRealSlice hm (pathExt hf hdec hν hk hle t) := fun y i =>
  fourierInv_im_eq_zero (refl_pathExt hf hdec hν hk hle t) y i

lemma isRealSlice_mildSDeriv {k : ℕ} (hk : 2 ≤ k) {m : ℕ} (hm : 2 ≤ m) (hm2 : m + 2 ≤ k)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) (Tfeff hf hdec hν)) :
    IsRealSlice hm (mildSDeriv hk hm2 hν (Tfeff_nonneg hf hdec hν)
        (FeffermanSobolev.toHmFeff u₀ hf hdec (k + 1)) (persistPath hf hdec hν hk) t) := by
  intro y i
  refine fourierInv_im_eq_zero ?_ y i
  have hd := hasDerivWithinAt_pathExt hf hdec hν hk hm2 ht
  have hd' := (refl m).hasFDerivAt.comp_hasDerivWithinAt t hd
  have hfun : (refl m) ∘ pathExt hf hdec hν hk (le_succ_of_add_two_le hm2) =
      pathExt hf hdec hν hk (le_succ_of_add_two_le hm2) :=
    funext fun s => refl_pathExt hf hdec hν hk _ s
  rw [hfun] at hd'
  exact UniqueDiffWithinAt.eq_deriv _ (uniqueDiffOn_Ico 0 _ t ht) hd' hd

lemma physicalMild_eq_pathExt {k : ℕ} (hk : 2 ≤ k) {m : ℕ} (hle : m ≤ k + 1) (s : ℝ) :
    physicalMild hf hdec hν s = physicalOfHm (pathExt hf hdec hν hk hle s) :=
  physicalMild_eq_inclExt hf hdec hν hk hle s

/-- The one-sided time derivative of the realized mild field at `t ∈ [0, T)`
is the physical field of the Fourier-side time derivative, for any index. -/
theorem timeSliceDeriv_physicalMild {k : ℕ} (hk : 2 ≤ k) {m : ℕ} (hm : 2 ≤ m)
    (hm2 : m + 2 ≤ k) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) (Tfeff hf hdec hν)) :
    KatoPonce.timeSliceDeriv (physicalMild hf hdec hν) t =
      physicalOfHm (mildSDeriv hk hm2 hν (Tfeff_nonneg hf hdec hν)
        (FeffermanSobolev.toHmFeff u₀ hf hdec (k + 1)) (persistPath hf hdec hν hk) t) := by
  funext x
  set L : Hm m →L[ℝ] E3 := realifyCLM.comp (evMap hm x)
  have hfun : (fun s => physicalMild hf hdec hν s x) =
      fun s => L (pathExt hf hdec hν hk (le_succ_of_add_two_le hm2) s) := by
    funext s
    rw [physicalMild_eq_pathExt hf hdec hν hk (le_succ_of_add_two_le hm2) s]
    rfl
  have hmem : Ico 0 (Tfeff hf hdec hν) ∈ 𝓝[Ici 0] t := by
    rw [← Ici_inter_Iio]
    exact inter_mem_nhdsWithin _ (Iio_mem_nhds ht.2)
  have hder := (L.hasFDerivAt.comp_hasDerivWithinAt t
    (hasDerivWithinAt_pathExt hf hdec hν hk hm2 ht)).mono_of_mem_nhdsWithin hmem
  unfold KatoPonce.timeSliceDeriv
  rw [hfun]
  exact hder.derivWithin (uniqueDiffOn_Ici 0 t ht.1)

theorem hsSq_physicalMild (t : ℝ) :
    R3BKM.hsSq 3 (physicalMild hf hdec hν t) =
      ‖incl (by norm_num : 3 ≤ 5) (pathExt hf hdec hν (by norm_num : 2 ≤ 7)
        (by norm_num : 5 ≤ 7 + 1) t)‖ ^ 2 := by
  rw [physicalMild_eq_pathExt hf hdec hν (by norm_num : 2 ≤ 7) (by norm_num : 5 ≤ 7 + 1) t,
    hsSq_physicalOfHm (le_refl 5)
      (isRealSlice_pathExt hf hdec hν (by norm_num) (by norm_num) _ t)]

/-- **Item 4.** The realized mild field satisfies the `H³` energy
right-derivative formula on `[0, Tfeff)`. -/
theorem h3EnergyRightDerivativeFormula_physicalMild :
    KatoPonce.H3EnergyRightDerivativeFormula (Tfeff hf hdec hν) (physicalMild hf hdec hν) := by
  have hk7 : 2 ≤ 7 := by norm_num
  have hm2 : 5 + 2 ≤ 7 := le_refl 7
  have hle : 5 ≤ 7 + 1 := by norm_num
  refine ⟨?_, ?_, ?_⟩
  · intro s hs _ k hk α
    have hk' : k + 2 ≤ 5 := by have := Finset.mem_range.1 hk; omega
    rw [physicalMild_eq_pathExt hf hdec hν hk7 hle s,
      timeSliceDeriv_physicalMild hf hdec hν hk7 (by norm_num) hm2 hs]
    exact integrable_inner_wordDeriv hk'
      (isRealSlice_pathExt hf hdec hν hk7 (by norm_num) hle s) _ α
  · intro s hs
    refine contDiff_infty.2 fun n => ?_
    rw [timeSliceDeriv_physicalMild hf hdec hν (by omega : 2 ≤ n + 4) (by omega : 2 ≤ n + 2)
      (le_refl (n + 4)) hs]
    exact contDiff_physicalOfHm (le_refl _) _
  · intro s hs _
    set Γ := pathExt hf hdec hν hk7 hle
    set D := mildSDeriv hk7 hm2 hν (Tfeff_nonneg hf hdec hν)
      (FeffermanSobolev.toHmFeff u₀ hf hdec (7 + 1)) (persistPath hf hdec hν hk7) s
    have hfun : (fun t => R3BKM.hsSq 3 (physicalMild hf hdec hν t)) =
        fun t => Complex.reCLM (inner ℂ (incl (by norm_num : 3 ≤ 5) (Γ t))
          (incl (by norm_num : 3 ≤ 5) (Γ t))) := by
      funext t
      rw [hsSq_physicalMild, Complex.reCLM_apply, ← inner_self_eq_norm_sq (𝕜 := ℂ)]
      rfl
    have hI : HasDerivWithinAt (fun t => incl (by norm_num : 3 ≤ 5) (Γ t))
        (incl (by norm_num : 3 ≤ 5) D) (Ico 0 (Tfeff hf hdec hν)) s :=
      (inclR (by norm_num : 3 ≤ 5)).hasFDerivAt.comp_hasDerivWithinAt s
        (hasDerivWithinAt_pathExt hf hdec hν hk7 hm2 hs)
    have hmem : Ico 0 (Tfeff hf hdec hν) ∈ 𝓝[Ici s] s := by
      refine mem_of_superset (inter_mem_nhdsWithin (Ici s) (Iio_mem_nhds hs.2)) ?_
      intro t ht
      exact ⟨hs.1.trans ht.1, ht.2⟩
    have hN := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt s
      ((hI.inner ℂ hI).mono_of_mem_nhdsWithin hmem)
    rw [hfun]
    convert hN using 1
    have hp := physical_pairing_eq (le_refl 5) (B := D)
      (isRealSlice_pathExt hf hdec hν hk7 (by norm_num) hle s)
    rw [KatoPonce.h3EnergyPairing, physicalMild_eq_pathExt hf hdec hν hk7 hle s,
      timeSliceDeriv_physicalMild hf hdec hν hk7 (by norm_num) hm2 hs]
    refine (congrArg (fun r => 2 * r) hp).trans ?_
    simp only [Complex.reCLM_apply, Complex.add_re]
    rw [← inner_conj_symm (incl (by norm_num : 3 ≤ 5) D) (incl (by norm_num : 3 ≤ 5) (Γ s)),
      Complex.conj_re]
    ring

end MildPath

#print axioms MildEnergy.integral_inner_fourierInvBCF
#print axioms MildEnergy.dw_fourierInvBCF
#print axioms MildEnergy.integral_inner_wordDeriv
#print axioms MildEnergy.physical_pairing_eq
#print axioms MildEnergy.sobolevEnergy_physicalOfHm
#print axioms MildEnergy.hsSq_physicalOfHm
#print axioms MildEnergy.timeSliceDeriv_physicalMild
#print axioms MildEnergy.hsSq_physicalMild
#print axioms MildEnergy.h3EnergyRightDerivativeFormula_physicalMild

end MildEnergy
