import Scratch.InverseSobolev
import Scratch.NonlinearSmooth
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-! # Inverse Fourier as a bounded linear map `Ĥ^m → (ℝ³ →ᵇ ℂ³)`

For `m ≥ 2`, an `Ĥ^m` representative is unweighted-integrable, so its
inverse Fourier transform is a bounded continuous function, and the map
is bounded linear. Evaluation is therefore jointly continuous in the
representative and the spatial variable. -/

open MeasureTheory FourierTransform Real Filter Topology Set BoundedContinuousFunction
open scoped ENNReal

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section
namespace FourierInvBCF

open LerayHeat SobolevHilbert InverseSobolev NonlinearSmooth

/-- The inverse Fourier transform is pointwise bounded by the `L¹` norm. -/
lemma norm_fourierInv_le (f : E3 → V) (x : E3) :
    ‖𝓕⁻ f x‖ ≤ ∫ ξ, ‖f ξ‖ := by
  rw [fourierInv_eq_fourier_neg, fourier_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp_rw [Circle.norm_smul]

/-- Inverse Fourier of an `Ĥ^m` representative, as a bounded continuous function. -/
def fourierInvBCF {m : ℕ} (hm : 2 ≤ m) (G : Hm m) : E3 →ᵇ V :=
  ofNormedAddCommGroup (𝓕⁻ (G : E3 → V))
    (contDiff_fourierInv_of_Hm (n := 0) (by omega) G).continuous
    (∫ ξ, ‖(G : E3 → V) ξ‖)
    (fun x => norm_fourierInv_le (G : E3 → V) x)

lemma coe_fourierInvBCF {m : ℕ} (hm : 2 ≤ m) (G : Hm m) :
    (fourierInvBCF hm G : E3 → V) = 𝓕⁻ (G : E3 → V) :=
  rfl

lemma norm_fourierInvBCF_le {m : ℕ} (hm : 2 ≤ m) (G : Hm m) :
    ‖fourierInvBCF hm G‖ ≤
      Real.sqrt (∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * 0) / FourierEmb.w ξ ^ m)).toReal *
        Real.sqrt ((2 : ℝ) ^ m) * ‖G‖ := by
  have hC : 0 ≤ ∫ ξ, ‖(G : E3 → V) ξ‖ :=
    integral_nonneg fun _ => norm_nonneg _
  exact (norm_ofNormedAddCommGroup_le
      (contDiff_fourierInv_of_Hm (n := 0) (by omega) G).continuous hC
      (fun x => norm_fourierInv_le (G : E3 → V) x)).trans
    (integral_norm_coeFn_le hm G)

/-- The map `G ↦ 𝓕⁻ G`, as a bounded linear map `Ĥ^m → (ℝ³ →ᵇ ℂ³)`. -/
lemma isBoundedLinearMap_fourierInvBCF {m : ℕ} (hm : 2 ≤ m) :
    IsBoundedLinearMap ℝ (fun G : Hm m => fourierInvBCF hm G) where
  map_add := by
    intro G H
    refine BoundedContinuousFunction.ext fun x => ?_
    have hae := (Lp.coeFn_add G H).filter_mono
      (Measure.AbsolutelyContinuous.ae_le (ac_vol m))
    have hGint := integrable_of_Hm hm G
    have hHint := integrable_of_Hm hm H
    have hsum :
        𝓕⁻ ((G + H : Hm m) : E3 → V) x =
          𝓕⁻ (G : E3 → V) x + 𝓕⁻ (H : E3 → V) x := by
      rw [fourierInv_congr_ae hae x]
      simp only [fourierInv_eq_fourier_neg, fourier_eq, Pi.add_apply, smul_add]
      exact integral_add
        ((fourierIntegral_convergent_iff (-x)).mpr hGint)
        ((fourierIntegral_convergent_iff (-x)).mpr hHint)
    simpa [fourierInvBCF] using hsum
  map_smul := by
    intro c G
    refine BoundedContinuousFunction.ext fun x => ?_
    have hreal : (c • G : Hm m) = (c : ℂ) • G := real_smul_eq_coe_smul c G
    have hae := (Lp.coeFn_smul (c : ℂ) G).filter_mono
      (Measure.AbsolutelyContinuous.ae_le (ac_vol m))
    have hsmul :
        𝓕⁻ ((c • G : Hm m) : E3 → V) x = c • 𝓕⁻ (G : E3 → V) x := by
      rw [hreal, fourierInv_congr_ae hae x]
      simp only [fourierInv_eq_fourier_neg, fourier_eq, Pi.smul_apply]
      have hcomm :
          (fun v : E3 => 𝐞 (-inner (𝕜 := ℝ) v (-x)) • (c : ℂ) • (G : E3 → V) v) =
            fun v => (c : ℂ) • 𝐞 (-inner (𝕜 := ℝ) v (-x)) • (G : E3 → V) v :=
        funext fun v => smul_comm _ _ _
      rw [hcomm, integral_smul]
      exact (real_smul_eq_coe_smul_V c _).symm
    simpa [fourierInvBCF] using hsmul
  bound := by
    refine ⟨max (Real.sqrt (∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * 0) / FourierEmb.w ξ ^ m)).toReal *
        Real.sqrt ((2 : ℝ) ^ m)) 1,
      lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun G => ?_⟩
    exact (norm_fourierInvBCF_le hm G).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg G))

/-- Evaluation of the inverse Fourier transform is jointly continuous in the
`Ĥ^m` representative and the spatial variable. -/
lemma continuous_uncurry_fourierInv {m : ℕ} (hm : 2 ≤ m) :
    Continuous (fun p : Hm m × E3 => 𝓕⁻ (p.1 : E3 → V) p.2) := by
  have hCLM : Continuous (fun G : Hm m => fourierInvBCF hm G) :=
    (isBoundedLinearMap_fourierInvBCF hm).toContinuousLinearMap.continuous
  have hev : Continuous (fun p : (E3 →ᵇ V) × E3 => (p.1 : E3 → V) p.2) :=
    continuous_eval
  exact hev.comp (hCLM.prodMap continuous_id)

#print axioms FourierInvBCF.norm_fourierInv_le
#print axioms FourierInvBCF.isBoundedLinearMap_fourierInvBCF
#print axioms FourierInvBCF.continuous_uncurry_fourierInv

/-- Post-composing the uncurried inverse Fourier transform with a continuous
linear map (e.g. taking real parts) remains jointly continuous. -/
lemma continuous_uncurry_clm_fourierInv {m : ℕ} (hm : 2 ≤ m)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : V →L[ℝ] F) :
    Continuous (fun p : Hm m × E3 => L (𝓕⁻ (p.1 : E3 → V) p.2)) :=
  L.continuous.comp (continuous_uncurry_fourierInv hm)

/-- If `γ` is continuous on `[0, T)`, the uncurried field
`(x, t) ↦ L ((𝓕⁻ (γ t)) x)` is jointly continuous on `ℝ³ × [0, T)`.
The inverse Fourier transform is packaged as a bounded continuous
function so that the statement does not mention `𝓕⁻` in its type. -/
theorem continuousOn_uncurry_clm_fourierInvBCF {m : ℕ} (hm : 2 ≤ m)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : V →L[ℝ] F)
    {T : ℝ} {γ : ℝ → Hm m} (hγ : ContinuousOn γ (Ico 0 T)) :
    ContinuousOn (fun q : E3 × ℝ => L (fourierInvBCF hm (γ q.2) q.1))
      (univ ×ˢ Ico 0 T) := by
  have hC : ContinuousOn (fun p : (E3 →ᵇ V) × E3 => L (p.1 p.2)) univ :=
    (L.continuous.comp continuous_eval).continuousOn
  have hpath : ContinuousOn (fun q : E3 × ℝ => (fourierInvBCF hm (γ q.2), q.1))
      (univ ×ˢ Ico 0 T) :=
    (((isBoundedLinearMap_fourierInvBCF hm).toContinuousLinearMap.continuous.comp_continuousOn
        (hγ.comp continuousOn_snd fun q hq => hq.2))).prodMk continuousOn_fst
  exact hC.comp hpath fun _ _ => mem_univ _

#print axioms FourierInvBCF.continuous_uncurry_clm_fourierInv
#print axioms FourierInvBCF.continuousOn_uncurry_clm_fourierInvBCF

end FourierInvBCF
