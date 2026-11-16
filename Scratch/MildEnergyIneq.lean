import Scratch.MildEnergy
import Scratch.IBPWholeSpace
import Scratch.MildDivFree

/-! # The energy inequality for the realized mild field

The nonlinearity does no work, `∫ ⟨u, (u·∇)u⟩ = 0` for a bounded,
divergence-free `C¹` field with `u, ∇u ∈ L²`; on the Fourier side the Leray
projector is self-adjoint and fixes the slice, and the Laplacian is
dissipative.  Hence the `L²` energy of the mild path is non-increasing. -/

open MeasureTheory Real Filter Topology Set FourierTransform
open scoped ENNReal ContDiff

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
namespace MildEnergyIneq

open NavierStokes3D IBPWholeSpace

lemma fderiv_coord {u : VelocityField} {x : T3} (hu : DifferentiableAt ℝ u x) (j : Fin 3)
    (v : T3) : fderiv ℝ (fun y => u y j) x v = fderiv ℝ u x v j := by
  have h := ((EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp x hu.hasFDerivAt)
  rw [show (fun y => u y j) = (EuclideanSpace.proj (𝕜 := ℝ) j) ∘ u from rfl, h.fderiv]
  rfl

lemma expand_e (v : T3) : v = ∑ j : Fin 3, v j • e j := by
  ext i
  simp [e, Pi.single_apply]

/-- **The nonlinearity does no work.** -/
theorem integral_inner_convective_eq_zero {u : VelocityField} (hu : ContDiff ℝ 1 u)
    (hdiv : ∀ x, div u x = 0) {C : ℝ} (hC : ∀ x, ‖u x‖ ≤ C) (hL2 : MemLp u 2)
    (hdL2 : ∀ j : Fin 3, MemLp (fun x => fderiv ℝ u x (e j)) 2) :
    ∫ x, inner ℝ (u x) (convective u u x) = 0 := by
  have hd : ∀ x, DifferentiableAt ℝ u x := fun x => hu.differentiable one_ne_zero x
  have hcd : Continuous fun x => fderiv ℝ u x := hu.continuous_fderiv one_ne_zero
  set φ : T3 → ℝ := fun x => (1 / 2 : ℝ) * inner ℝ (u x) (u x) with hφ
  have hφD : ∀ x, DifferentiableAt ℝ φ x := fun x =>
    (((hd x).inner ℝ (hd x))).const_mul _
  have hφj : ∀ x j, fderiv ℝ φ x (e j) = inner ℝ (u x) (fderiv ℝ u x (e j)) := by
    intro x j
    have h := ((hd x).hasFDerivAt.inner ℝ (hd x).hasFDerivAt).const_mul (1 / 2 : ℝ)
    rw [h.fderiv]
    simp [fderivInnerCLM_apply, real_inner_comm]
    ring
  have hcoord : ∀ x (j : Fin 3), |u x j| ≤ ‖u x‖ := fun x j => by
    simpa using PiLp.norm_apply_le (u x) j
  have hcoord' : ∀ x (j : Fin 3), |fderiv ℝ u x (e j) j| ≤ ‖fderiv ℝ u x (e j)‖ :=
    fun x j => by simpa using PiLp.norm_apply_le (fderiv ℝ u x (e j)) j
  have hnorm2 : Integrable fun x => ‖u x‖ ^ 2 := (memLp_two_iff_integrable_sq_norm
    hu.continuous.aestronglyMeasurable).1 hL2
  have hprod : ∀ j : Fin 3, Integrable fun x => ‖u x‖ * ‖fderiv ℝ u x (e j)‖ := fun j =>
    (hL2.norm.integrable_mul (hdL2 j).norm)
  have hcj : ∀ j : Fin 3, Continuous fun x => fderiv ℝ u x (e j) := fun j =>
    hcd.clm_apply continuous_const
  have hcu : ∀ j : Fin 3, Continuous fun x => u x j := fun j =>
    (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp hu.continuous
  have hcφ : Continuous φ := continuous_const.mul (hu.continuous.inner hu.continuous)
  have hφb : ∀ x, |φ x| ≤ (1 / 2) * (C * ‖u x‖) := fun x => by
    simp only [hφ, real_inner_self_eq_norm_sq, abs_mul]
    rw [abs_of_pos (by norm_num : (0:ℝ) < 1 / 2), abs_of_nonneg (by positivity)]
    gcongr
    rw [sq]; exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
  have hgd : ∀ (j : Fin 3) x, DifferentiableAt ℝ (fun y => u y j) x := fun j x =>
    ((EuclideanSpace.proj (𝕜 := ℝ) j).differentiableAt).comp x (hd x)
  have hI1 : ∀ j : Fin 3, Integrable fun x => fderiv ℝ φ x (e j) * u x j := by
    intro j
    refine ((hprod j).const_mul C).mono ?_ (Eventually.of_forall fun x => ?_)
    · simp only [hφj]
      exact ((hu.continuous.inner (hcj j)).mul (hcu j)).aestronglyMeasurable
    · rw [hφj, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        Real.norm_of_nonneg (by have := (norm_nonneg (u x)).trans (hC x); positivity)]
      calc |inner ℝ (u x) (fderiv ℝ u x (e j))| * |u x j|
          ≤ (‖u x‖ * ‖fderiv ℝ u x (e j)‖) * C :=
            mul_le_mul (abs_real_inner_le_norm _ _) ((hcoord x j).trans (hC x))
              (abs_nonneg _) (by positivity)
        _ = _ := by ring
  have hI2 : ∀ j : Fin 3, Integrable fun x => φ x * fderiv ℝ (fun y => u y j) x (e j) := by
    intro j
    refine (((hprod j).const_mul C).const_mul (1 / 2)).mono ?_
      (Eventually.of_forall fun x => ?_)
    · simp only [fderiv_coord (hd _)]
      exact (hcφ.mul ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp
        (hcj j))).aestronglyMeasurable
    · rw [fderiv_coord (hd x), norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        Real.norm_of_nonneg (by have := (norm_nonneg (u x)).trans (hC x); positivity)]
      calc |φ x| * |fderiv ℝ u x (e j) j|
          ≤ ((1 / 2) * (C * ‖u x‖)) * ‖fderiv ℝ u x (e j)‖ :=
            mul_le_mul (hφb x) (hcoord' x j) (abs_nonneg _) (by
              have := (norm_nonneg (u x)).trans (hC x); positivity)
        _ = _ := by ring
  have hI3 : ∀ j : Fin 3, Integrable fun x => φ x * u x j := by
    intro j
    refine ((hnorm2.const_mul C).const_mul (1 / 2)).mono (hcφ.mul (hcu j)).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      Real.norm_of_nonneg (by have := (norm_nonneg (u x)).trans (hC x); positivity)]
    calc |φ x| * |u x j| ≤ ((1 / 2) * (C * ‖u x‖)) * ‖u x‖ :=
          mul_le_mul (hφb x) (hcoord x j) (abs_nonneg _) (by
            have := (norm_nonneg (u x)).trans (hC x); positivity)
      _ = _ := by ring
  have hpt : ∀ x, inner ℝ (u x) (convective u u x) =
      ∑ j : Fin 3, fderiv ℝ φ x (e j) * u x j := by
    intro x
    have h : fderiv ℝ u x (u x) = ∑ j : Fin 3, u x j • fderiv ℝ u x (e j) := by
      conv_lhs => rw [expand_e (u x)]
      simp only [map_sum, map_smul]
    simp only [convective, hφj, h, inner_sum, inner_smul_right]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hibp : ∀ j : Fin 3, ∫ x, fderiv ℝ φ x (e j) * u x j =
      -∫ x, φ x * fderiv ℝ (fun y => u y j) x (e j) := fun j =>
    integral_partial_mul j (hI1 j) (hI2 j) (hI3 j) hφD (hgd j)
  calc ∫ x, inner ℝ (u x) (convective u u x)
      = ∑ j : Fin 3, ∫ x, fderiv ℝ φ x (e j) * u x j := by
        simp only [hpt]; exact integral_finset_sum _ fun j _ => hI1 j
    _ = -∫ x, φ x * div u x := by
        have h : ∀ x, φ x * div u x =
            ∑ j : Fin 3, φ x * fderiv ℝ (fun y => u y j) x (e j) := fun x => by
          simp only [div, Finset.mul_sum]; rfl
        simp only [h]
        rw [integral_finset_sum _ fun j _ => hI2 j, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun j _ => hibp j
    _ = 0 := by simp [hdiv]


/-! ## The nonlinearity on the Fourier side -/

open LerayHeat SobolevFourier SobolevHilbert InverseSobolev LerayPressure FourierInvBCF
  FeffermanMild MildEnergy MildMomentum NonlinearHm ProductHm PlancherelBridge

lemma memLp_physicalOfHm {m : ℕ} (hm : 2 ≤ m) (G : Hm m) : MemLp (physicalOfHm G) 2 := by
  refine (memLp_fourierInvBCF hm G).of_le ?_ (Eventually.of_forall fun x => ?_)
  · exact (contDiff_physicalOfHm (n := 0) (by omega) G).continuous.aestronglyMeasurable
  · exact norm_realify_le _

lemma norm_physicalOfHm_le {m : ℕ} (hm : 2 ≤ m) (G : Hm m) (x : E3) :
    ‖physicalOfHm G x‖ ≤ ‖fourierInvBCF hm G‖ :=
  (norm_realify_le _).trans ((fourierInvBCF hm G).norm_coe_le_norm x)

/-- For a real, Leray-fixed slice `U ∈ Ĥ³`, `Re ∫ ⟨U, N(U)⟩ dξ = 0`. -/
theorem re_integral_inner_NSN_eq_zero {U : Hm 3} (hdiv : lerayH 3 U = U)
    (hreal : ∀ y : E3, ∀ k : Fin 3, (𝓕⁻ (U : E3 → V) y k).im = 0) :
    (∫ ξ, inner ℂ ((U : E3 → V) ξ) (((NSN (le_refl 3) U : Hm (3 - 1)) : E3 → V) ξ)).re = 0 := by
  set Dt : Hm (3 - 1) := divTensor (le_refl 3) U
  have hfixU : (U : E3 → V) =ᵐ[MeasureTheory.volume] fun ξ => lerSym ξ ((U : E3 → V) ξ) := by
    have h := (MildDivFree.coeFn_lerayH 3 U).filter_mono (Measure.AbsolutelyContinuous.ae_le (ac_vol 3))
    rw [hdiv] at h
    exact h
  have hN : ((NSN (le_refl 3) U : Hm (3 - 1)) : E3 → V) =ᵐ[MeasureTheory.volume]
      fun ξ => lerSym ξ ((Dt : E3 → V) ξ) :=
    (MildDivFree.coeFn_lerayH (3 - 1) Dt).filter_mono (Measure.AbsolutelyContinuous.ae_le (ac_vol (3 - 1)))
  have h1 : ∫ ξ, inner ℂ ((U : E3 → V) ξ) (((NSN (le_refl 3) U : Hm (3 - 1)) : E3 → V) ξ) =
      ∫ ξ, inner ℂ ((U : E3 → V) ξ) ((Dt : E3 → V) ξ) := by
    refine integral_congr_ae ?_
    filter_upwards [hfixU, hN] with ξ hu hn
    rw [hn, ← lerSym_selfAdj, ← hu]
  have h2 := integral_inner_fourierInvBCF (by norm_num : 2 ≤ 3) (by norm_num : 2 ≤ 3 - 1) U Dt
  set u := physicalOfHm U
  have hcub : ∫ x, inner ℝ (u x) (NavierStokes3D.convective u u x) = 0 := by
    refine integral_inner_convective_eq_zero (contDiff_physicalOfHm (n := 1) (le_refl 3) U)
      (MildDivFree.div_physicalOfHm_of_lerayH (le_refl 3) hdiv)
      (norm_physicalOfHm_le (by norm_num) U) (memLp_physicalOfHm (by norm_num) U) fun j => ?_
    have h := fderiv_physicalOfHm_single (le_refl 3) U j
    have h' : (fun x => fderiv ℝ u x (e j)) = physicalOfHm (dH (by norm_num : 1 ≤ 3) j U) := h
    rw [h']
    exact memLp_physicalOfHm (le_refl 2) _
  rw [h1, ← h2, ← RCLike.re_to_complex]
  refine Eq.trans (integral_re (integrable_inner_fourierInvBCF _ _ U Dt)).symm ?_
  rw [← hcub]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [RCLike.re_to_complex]
  have hr := inner_realify_of_real (w := 𝓕⁻ ((Dt : Hm (3 - 1)) : E3 → V) x) (hreal x)
  have hc := realify_fourierInv_divTensor (le_refl 3) hdiv hreal x
  refine hr.symm.trans ?_
  exact congrArg (inner ℝ (u x)) hc


/-! ## `L²` energy of a slice -/

lemma sobW_zero : sobW 0 = fun _ => 1 := by
  funext ξ; simp [sobW]

lemma inner_incl_zero {m n : ℕ} (hm : 0 ≤ m) (hn : 0 ≤ n) (A : Hm m) (B : Hm n) :
    inner ℂ (incl hm A) (incl hn B) =
      ∫ ξ, inner ℂ ((A : E3 → V) ξ) ((B : E3 → V) ξ) := by
  rw [MeasureTheory.L2.inner_def]
  have hμ : μw 0 = MeasureTheory.volume := by
    rw [μw, sobW_zero]; exact withDensity_one
  have h1 := ProductHm.coeFn_incl hm A
  have h2 := ProductHm.coeFn_incl hn B
  rw [integral_congr_ae (by filter_upwards [h1, h2] with ξ h1 h2; rw [h1, h2])]
  rw [hμ]
  rfl

lemma re_inner_incl_zero_self {m : ℕ} (hm : 0 ≤ m) (A : Hm m) :
    (inner ℂ (incl hm A) (incl hm A)).re = ∫ ξ, ‖(A : E3 → V) ξ‖ ^ 2 := by
  rw [inner_incl_zero, ← RCLike.re_to_complex]
  refine Eq.trans (integral_re (integrable_inner_Hm A A)).symm ?_
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

/-- **`L²` energy of a real slice** (`m ≥ 2`): `∫⁻ |u_A|² = Re ⟨A, A⟩_{L²}`. -/
theorem lintegral_physicalOfHm_sq {m : ℕ} (hm : 2 ≤ m) {A : Hm m} (hA : IsRealSlice hm A) :
    ∫⁻ x, ‖physicalOfHm A x‖ₑ ^ 2 =
      ENNReal.ofReal (inner ℂ (incl (Nat.zero_le m) A) (incl (Nat.zero_le m) A)).re := by
  have hpt : ∀ x, ‖physicalOfHm A x‖ₑ = ‖fourierInvBCF hm A x‖ₑ := fun x => by
    have h := congrFun (fourierInvBCF_eq_cplx hm hA) x
    rw [h, Function.comp_apply]
    simp only [← ofReal_norm_eq_enorm, norm_cplx]
  simp only [hpt]
  rw [lintegral_fourierInvBCF_sq hm A, re_inner_incl_zero_self]
  have hint : Integrable fun ξ => ‖(A : E3 → V) ξ‖ ^ 2 :=
    (memLp_two_iff_integrable_sq_norm (memLp_coe_Hm A).1).1 (memLp_coe_Hm A)
  rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ξ => by positivity)]
  refine lintegral_congr fun ξ => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]


/-! ## Along the mild path -/

section MildPath

open MildTimeDeriv MildPathSmooth RepairedTether HeatDeriv MildReal MildExistence
  PersistenceHm FeffermanSobolev

variable {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀) (hdec : FeffermanDecay u₀)
  {ν : ℝ} (hν : 0 < ν)

/-- **Dissipation.** Along the mild path, `Re ⟨u, ∂ₜu⟩_{L²} ≤ 0`. -/
theorem re_inner_mildSDeriv_nonpos (hdiv : ∀ x, div u₀ x = 0) {s : ℝ} (hs : s ∈ Ico (0 : ℝ) (Tfeff hf hdec hν)) :
    (inner ℂ (incl (Nat.zero_le 2) (pathExt hf hdec hν (by norm_num : 2 ≤ 4)
        (le_succ_of_add_two_le (le_refl 4)) s))
      (incl (Nat.zero_le 2) (mildSDeriv (by norm_num : 2 ≤ 4) (le_refl (2 + 2)) hν
        (Tfeff_nonneg hf hdec hν) (toHmFeff u₀ hf hdec (4 + 1))
        (persistPath hf hdec hν (by norm_num : 2 ≤ 4)) s))).re ≤ 0 := by
  have hT := Tfeff_nonneg hf hdec hν
  have hk4 : 2 ≤ 4 := by norm_num
  set P : Hm (4 + 1) := ContinuousMap.IccExtend hT (persistPath hf hdec hν hk4) s with hP
  set Q' : Hm 3 := ContinuousMap.IccExtend hT (persistPath hf hdec hν (by norm_num : 2 ≤ 2)) s
  have hD := mildSDeriv_eq_NSNsucc hk4 (le_refl 2) (le_refl (2 + 2)) hν hT
    (persistPath_mildS hf hdec hν hk4) (Ico_subset_Icc_self hs)
  rw [hD, inner_incl_zero, ← RCLike.re_to_complex]
  set L := inclExt (add_two_le_succ (le_refl (2 + 2))) hT (persistPath hf hdec hν hk4) s
  set Q := inclExt (InclNSN.le_succ_succ (InclNSN.le_of_add_two_le (le_refl (2 + 2)))) hT
    (persistPath hf hdec hν hk4) s
  set Γ := pathExt hf hdec hν hk4 (le_succ_of_add_two_le (le_refl 4)) s
  set N := NSNsucc (le_refl 2) Q
  have hQ : Q = Q' := inclExt_three_eq hf hdec hν hk4 _ s
  have hΓP : (Γ : E3 → V) =ᵐ[MeasureTheory.volume] (P : E3 → V) := coeFn_incl_vol _ _
  have hLP : (L : E3 → V) =ᵐ[MeasureTheory.volume] (P : E3 → V) := coeFn_incl_vol _ _
  have hQP : (Q : E3 → V) =ᵐ[MeasureTheory.volume] (P : E3 → V) := coeFn_incl_vol _ _
  have hlap := (coeFn_lapH 2 L).filter_mono (Measure.AbsolutelyContinuous.ae_le (ac_vol 2))
  have hsub := (Lp.coeFn_sub (ν • lapH 2 L) N).filter_mono
    (Measure.AbsolutelyContinuous.ae_le (ac_vol 2))
  have hsm := (Lp.coeFn_smul ν (lapH 2 L)).filter_mono
    (Measure.AbsolutelyContinuous.ae_le (ac_vol 2))
  set f1 : E3 → ℝ := fun ξ => ν * (inner ℂ ((Γ : E3 → V) ξ) ((lapH 2 L : E3 → V) ξ)).re
  set f2 : E3 → ℝ := fun ξ => (inner ℂ ((Q : E3 → V) ξ) ((N : E3 → V) ξ)).re
  have hi1 : Integrable f1 := ((integrable_inner_Hm Γ (lapH 2 L)).re).const_mul ν
  have hi2 : Integrable f2 := (integrable_inner_Hm Q N).re
  refine Eq.trans_le (integral_re (integrable_inner_Hm Γ (ν • lapH 2 L - N))).symm ?_
  have hcongr : (fun ξ => RCLike.re (inner ℂ ((Γ : E3 → V) ξ)
      ((((ν • lapH 2 L - N : Hm 2)) : E3 → V) ξ))) =ᵐ[MeasureTheory.volume] f1 - f2 := by
    filter_upwards [hsub, hsm, hΓP, hQP] with ξ h1 h2 h3 h4
    simp only [Pi.sub_apply, f1, f2]
    rw [h1, Pi.sub_apply, h2, Pi.smul_apply, inner_sub_right, h3, ← h4,
      RCLike.re_to_complex, Complex.sub_re]
    congr 1
    rw [← Complex.coe_smul, inner_smul_right, Complex.re_ofReal_mul]
  rw [integral_congr_ae hcongr]
  refine (integral_sub hi1 hi2).trans_le ?_
  have key : ∀ U : Hm 3, lerayH 3 U = U →
      (∀ y : E3, ∀ k : Fin 3, (𝓕⁻ (U : E3 → V) y k).im = 0) →
      ∫ ξ, (inner ℂ ((U : E3 → V) ξ) ((NSNsucc (le_refl 2) U : Hm 2) ξ)).re = 0 := by
    intro U h1 h2
    have h := re_integral_inner_NSN_eq_zero h1 h2
    rw [← RCLike.re_to_complex] at h
    refine (integral_re (integrable_inner_Hm U (NSNsucc (le_refl 2) U))).trans ?_
    rw [coe_NSNsucc]
    exact h
  have h2z : ∫ ξ, f2 ξ = 0 := by
    refine key Q ?_ ?_
    · rw [hQ]; exact lerayH_IccExtend hf hdec hdiv hν s
    · rw [hQ]; exact fun y k => fourierInv_IccExtend_im hf hdec hν s y k
  rw [h2z, sub_zero]
  refine integral_nonpos_of_ae ?_
  filter_upwards [hlap, hΓP, hLP] with ξ h1 h2 h3
  simp only [f1, Pi.zero_apply]
  rw [h1, h2, h3, inner_smul_right, ← Complex.ofReal_neg, Complex.re_ofReal_mul,
    ← RCLike.re_to_complex, inner_self_eq_norm_sq (𝕜 := ℂ)]
  have : 0 ≤ 4 * π ^ 2 * ‖ξ‖ ^ 2 * ‖(P : E3 → V) ξ‖ ^ 2 := by positivity
  nlinarith [hν]

/-- **Item 5: the energy inequality** for the realized mild field of
divergence-free Fefferman data: `∫ |u(t)|² ≤ ∫ |u°|²` for `t ∈ [0, Tfeff)`. -/
theorem energyInequality_physicalMild (hdiv : ∀ x, div u₀ x = 0) :
    ∀ t ∈ Ico (0 : ℝ) (Tfeff hf hdec hν),
      ∫⁻ x, ‖physicalMild hf hdec hν t x‖ₑ ^ 2 ≤ ∫⁻ x, ‖u₀ x‖ₑ ^ 2 := by
  have hk4 : 2 ≤ 4 := by norm_num
  have hm2 : 2 + 2 ≤ 4 := le_refl 4
  have hle : 2 ≤ 4 + 1 := le_succ_of_add_two_le hm2
  have h0 : 0 ≤ 2 := Nat.zero_le 2
  set Γ := pathExt hf hdec hν hk4 hle
  set g : ℝ → ℝ := fun t => Complex.reCLM (inner ℂ (incl h0 (Γ t)) (incl h0 (Γ t))) with hg
  have hE : ∀ t, ∫⁻ x, ‖physicalMild hf hdec hν t x‖ₑ ^ 2 = ENNReal.ofReal (g t) := by
    intro t
    rw [physicalMild_eq_pathExt hf hdec hν hk4 hle t]
    exact lintegral_physicalOfHm_sq (le_refl 2) (isRealSlice_pathExt hf hdec hν hk4 (le_refl 2) hle t)
  set D := fun s => mildSDeriv hk4 hm2 hν (Tfeff_nonneg hf hdec hν)
    (toHmFeff u₀ hf hdec (4 + 1)) (persistPath hf hdec hν hk4) s
  set g' : ℝ → ℝ := fun s => Complex.reCLM (inner ℂ (incl h0 (Γ s)) (incl h0 (D s)) +
    inner ℂ (incl h0 (D s)) (incl h0 (Γ s))) with hg'
  have hder : ∀ s ∈ Ico (0 : ℝ) (Tfeff hf hdec hν),
      HasDerivWithinAt g (g' s) (Ico 0 (Tfeff hf hdec hν)) s := by
    intro s hs
    have hI : HasDerivWithinAt (fun t => incl h0 (Γ t)) (incl h0 (D s))
        (Ico 0 (Tfeff hf hdec hν)) s :=
      (inclR h0).hasFDerivAt.comp_hasDerivWithinAt s
        (hasDerivWithinAt_pathExt hf hdec hν hk4 hm2 hs)
    have hN := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt s (hI.inner ℂ hI)
    convert hN using 1
  have hneg : ∀ s ∈ Ico (0 : ℝ) (Tfeff hf hdec hν), g' s ≤ 0 := by
    intro s hs
    have h := re_inner_mildSDeriv_nonpos hf hdec hν hdiv hs
    simp only [hg', Complex.reCLM_apply, Complex.add_re]
    rw [← inner_conj_symm (incl h0 (D s)) (incl h0 (Γ s)), Complex.conj_re]
    have h' : (inner ℂ (incl h0 (Γ s)) (incl h0 (D s))).re ≤ 0 := h
    linarith
  have hanti : AntitoneOn g (Ico 0 (Tfeff hf hdec hν)) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := g') (convex_Ico 0 _)
      (fun s hs => (hder s hs).continuousWithinAt) (fun s hs => ?_) (fun s hs => ?_)
    · rw [interior_Ico] at hs ⊢
      exact (hder s (Ioo_subset_Ico_self hs)).mono Ioo_subset_Ico_self
    · rw [interior_Ico] at hs
      exact hneg s (Ioo_subset_Ico_self hs)
  intro t ht
  have h0mem : (0 : ℝ) ∈ Ico (0 : ℝ) (Tfeff hf hdec hν) := ⟨le_rfl, ht.1.trans_lt ht.2⟩
  have hle0 := hanti h0mem ht ht.1
  rw [hE t, ← physicalMild_zero hf hdec hν, hE 0]
  exact ENNReal.ofReal_le_ofReal hle0

end MildPath

end MildEnergyIneq

#print axioms MildEnergyIneq.integral_inner_convective_eq_zero
#print axioms MildEnergyIneq.re_integral_inner_NSN_eq_zero
#print axioms MildEnergyIneq.lintegral_physicalOfHm_sq
#print axioms MildEnergyIneq.re_inner_mildSDeriv_nonpos
#print axioms MildEnergyIneq.energyInequality_physicalMild
