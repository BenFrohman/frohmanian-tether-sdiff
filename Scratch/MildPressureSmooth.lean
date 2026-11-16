import Scratch.MildEnergyIneq
import Scratch.MildJointSmoothInf
import Scratch.NonlinearSmooth

/-! # Joint `C^∞` of the Leray pressure along the mild path

The Fourier-side pressure `lerayPressureHm` is a continuous quadratic map on
`Ĥ^s`, hence `C^∞`; composed with the `C^n` mild path in `Ĥ^{n+3}` it is a
`C^n` path, and joint `C^n` of `(x, G) ↦ 𝓕⁻ G x` gives joint `C^n` of the
physical pressure.  The physical pressure depends on the slice only through
its a.e. class, so the index can be raised freely. -/

open MeasureTheory Real Filter Topology Set FourierTransform
open scoped ENNReal ContDiff Convolution

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
namespace MildPressureSmooth

open LerayHeat SobolevHilbert InverseSobolev LerayPressure FourierInvBCF FourierInvFDeriv
  FeffermanMild MildMomentum ProductHm NonlinearSmooth PersistenceHm MildTimeDeriv
  MildPathSmooth RepairedTether

/-- `lerayPressureHm : Ĥ^s → Ĥ^s` is `C^∞` (over `ℝ`). -/
theorem contDiff_lerayPressureHm {s : ℕ} (hs : 3 ≤ s) {n : WithTop ℕ∞} :
    ContDiff ℝ n (lerayPressureHm hs) := by
  unfold lerayPressureHm
  refine ContDiff.neg ?_
  refine ContDiff.sum (s := Finset.univ) fun i _ =>
    ContDiff.sum (s := Finset.univ) fun j _ => ?_
  exact (isBoundedLinearMap_restrictCLM (rieszMul i j s)
      real_smul_eq_coe_smul real_smul_eq_coe_smul).contDiff.comp
    (contDiff_mulF_quad hs (Lprod i j))

lemma cc_congr {F F' : E3 → V} (h : F =ᵐ[volume] F') (i j : Fin 3) (ξ : E3) :
    cc F F i j ξ = cc F' F' i j ξ := by
  unfold cc
  have h2 : (fun t => F (ξ - t)) =ᵐ[volume] fun t => F' (ξ - t) :=
    (Measure.measurePreserving_sub_left volume ξ).quasiMeasurePreserving.ae_eq h
  refine integral_congr_ae ?_
  filter_upwards [h, h2] with t h1 h2
  simp only [h1, h2]

/-- The physical Leray pressure depends only on the a.e. class of the slice. -/
theorem lerayPressure_congr {s s' : ℕ} (hs : 3 ≤ s) (hs' : 3 ≤ s') {U : Hm s} {U' : Hm s'}
    (h : (U : E3 → V) =ᵐ[volume] (U' : E3 → V)) :
    lerayPressure hs U = lerayPressure hs' U' := by
  funext x
  unfold lerayPressure
  rw [physicalInv_def, physicalInv_def, coe_fourierInvBCF, coe_fourierInvBCF]
  have hae : ((lerayPressureHm hs U : Hm s) : E3 → V) =ᵐ[volume]
      ((lerayPressureHm hs' U' : Hm s') : E3 → V) := by
    filter_upwards [coeFn_lerayPressureHm_vol hs U, coeFn_lerayPressureHm_vol hs' U'] with ξ h1 h2
    rw [h1, h2]
    simp only [cc_congr h]
  rw [fourierInv_congr_ae hae x]

variable {u₀ : NavierStokes3D.VelocityField} (hf : ContDiff ℝ ∞ u₀)
  (hdec : FeffermanDecay u₀) {ν : ℝ} (hν : 0 < ν)

/-- The mild pressure equals the Leray pressure of any included persisted slice. -/
lemma presMild_eq_inclExt {k : ℕ} (hk : 2 ≤ k) {m : ℕ} (hm : 3 ≤ m) (hle : m ≤ k + 1) (t : ℝ) :
    presMild hf hdec hν t =
      lerayPressure hm (inclExt hle (Tfeff_nonneg hf hdec hν) (persistPath hf hdec hν hk) t) := by
  have hT := Tfeff_nonneg hf hdec hν
  unfold presMild
  refine lerayPressure_congr _ _ ?_
  have h3 := inclExt_three_eq hf hdec hν hk (by omega : 3 ≤ k + 1) t
  have ha : ((inclExt (by omega : 3 ≤ k + 1) hT (persistPath hf hdec hν hk) t : Hm 3) :
      E3 → V) =ᵐ[volume] ((ContinuousMap.IccExtend hT (persistPath hf hdec hν hk) t :
        Hm (k + 1)) : E3 → V) := coeFn_incl_vol _ _
  have hb : ((inclExt hle hT (persistPath hf hdec hν hk) t : Hm m) : E3 → V) =ᵐ[volume]
      ((ContinuousMap.IccExtend hT (persistPath hf hdec hν hk) t : Hm (k + 1)) : E3 → V) :=
    coeFn_incl_vol _ _
  rw [h3] at ha
  exact ha.trans hb.symm

/-- **Joint `C^n` of the mild pressure** on `ℝ³ × [0, T)`, for every `n`. -/
theorem contDiffOn_presMild_nat (n : ℕ) :
    ContDiffOn ℝ n (fun q : E3 × ℝ => presMild hf hdec hν q.2 q.1)
      (univ ×ˢ Ico 0 (Tfeff hf hdec hν)) := by
  have hk : 2 ≤ 3 * n + 3 := by omega
  have hle : n + 3 ≤ 3 * n + 3 + 1 := by omega
  have hn : n + 3 + 2 * n ≤ 3 * n + 3 := by omega
  have hs3 : 3 ≤ n + 3 := by omega
  set γ := inclExt hle (Tfeff_nonneg hf hdec hν) (persistPath hf hdec hν hk)
  have hγ : ContDiffOn ℝ n γ (Ico 0 (Tfeff hf hdec hν)) :=
    contDiffOn_inclExt hk (by omega : 2 ≤ n + 3) hn hν
      (Tfeff_nonneg hf hdec hν) (persistPath_mildS hf hdec hν hk)
  have hP : ContDiffOn ℝ n (fun t => lerayPressureHm hs3 (γ t)) (Ico 0 (Tfeff hf hdec hν)) :=
    (contDiff_lerayPressureHm hs3).comp_contDiffOn hγ
  have hC := contDiffOn_uncurry_clm_path (le_refl (n + 3)) (Complex.reCLM.comp coord0ℝ) hP
  refine hC.congr ?_
  intro q _
  rw [presMild_eq_inclExt hf hdec hν hk hs3 hle q.2]
  unfold lerayPressure
  rw [physicalInv_def]
  rfl

theorem contDiffOn_presMild :
    ContDiffOn ℝ ∞ (fun q : E3 × ℝ => presMild hf hdec hν q.2 q.1)
      (univ ×ˢ Ico 0 (Tfeff hf hdec hν)) :=
  contDiffOn_infty.2 fun n => contDiffOn_presMild_nat hf hdec hν n

/-- **Item 6.** For divergence-free Fefferman data, the realized mild field
and its Leray pressure form a solution in Fefferman's smooth class on
`ℝ³ × [0, Tfeff)`. -/
theorem isFeffermanSolutionOn_physicalMild (hdiv : ∀ x, NavierStokes3D.div u₀ x = 0) :
    IsFeffermanSolutionOn ν (Tfeff hf hdec hν) u₀ (physicalMild hf hdec hν)
      (presMild hf hdec hν) :=
  ⟨MildJointSmooth.contDiffOn_physicalMild hf hdec hν,
    contDiffOn_presMild hf hdec hν,
    fun t ht x => ⟨momentum_physicalMild hf hdec hdiv hν ht x,
      MildDivFree.div_physicalMild hf hdec hdiv hν t x⟩,
    fun x => congrFun (physicalMild_zero hf hdec hν) x,
    MildEnergyIneq.energyInequality_physicalMild hf hdec hν hdiv⟩

end MildPressureSmooth

#print axioms MildPressureSmooth.contDiff_lerayPressureHm
#print axioms MildPressureSmooth.lerayPressure_congr
#print axioms MildPressureSmooth.presMild_eq_inclExt
#print axioms MildPressureSmooth.contDiffOn_presMild_nat
#print axioms MildPressureSmooth.contDiffOn_presMild
#print axioms MildPressureSmooth.isFeffermanSolutionOn_physicalMild
