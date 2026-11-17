/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import Scratch.FeffermanMild
import Scratch.FourierInvFDeriv

/-!
 # The realized mild field is divergence-free

The Leray projector `lerayH` commutes with the heat multipliers and with the
smoothing Duhamel integral, fixes the nonlinearity `NSN = lerayH ∘ divTensor`,
and fixes the Fourier representative of divergence-free Fefferman data.  Hence
every slice of the persisted mild path is a fixed point of `lerayH`, and the
physical divergence of a fixed point of `lerayH` vanishes identically.
-/

open MeasureTheory Real Filter Topology Set
open scoped ENNReal ContDiff

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
namespace MildDivFree

open LerayHeat SobolevFourier SobolevHilbert HeatSobolev Duhamel DuhamelUp
  MildExistence PersistenceHm NonlinearHm FeffermanMild

lemma coeFn_lerayH (m : ℕ) (G : Hm m) :
    (lerayH m G : E3 → V) =ᵐ[μw m] fun ξ => lerSym ξ ((G : E3 → V) ξ) := by
  simpa [lerayH] using
    coeFn_wmul lerSym lerSym_meas 1 zero_le_one (bound_one (m := m) lerSym_norm) G

lemma lerayH_heatH (m : ℕ) (τ : ℝ) (G : Hm m) :
    lerayH m (heatH m τ G) = heatH m τ (lerayH m G) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_lerayH m (heatH m τ G), coeFn_heatH τ G,
    coeFn_heatH τ (lerayH m G), coeFn_lerayH m G] with ξ h1 h2 h3 h4
  rw [h1, h2, h3, h4, map_smul]

lemma lerayH_heatUp (m : ℕ) {τ : ℝ} (hτ : 0 < τ) (G : Hm m) :
    lerayH (m + 1) (heatUp m hτ G) = heatUp m hτ (lerayH m G) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_lerayH (m + 1) (heatUp m hτ G), coeFn_heatUp hτ G,
    coeFn_heatUp hτ (lerayH m G), (ac_ww m (m + 1)).ae_le (coeFn_lerayH m G)]
    with ξ h1 h2 h3 h4
  rw [h1, h2, h3, h4, map_smul]

lemma lerayH_lerayH (m : ℕ) (G : Hm m) : lerayH m (lerayH m G) = lerayH m G := by
  refine Lp.ext ?_
  filter_upwards [coeFn_lerayH m (lerayH m G), coeFn_lerayH m G] with ξ h1 h2
  rw [h1, h2, lerSym_idem]

lemma lerayH_NSN {s : ℕ} (hs : 3 ≤ s) (u : Hm s) :
    lerayH (s - 1) (NSN hs u) = NSN hs u :=
  lerayH_lerayH (s - 1) _

lemma lerayH_upI {m : ℕ} (G : ℝ → Hm m) (t s : ℝ) :
    lerayH (m + 1) (upI G t s) = upI (fun r => lerayH m (G r)) t s := by
  unfold upI
  split_ifs with h
  · exact lerayH_heatUp m _ _
  · exact map_zero _

lemma lerayH_duhUp {m : ℕ} {G : ℝ → Hm m} (hG : Continuous G) {t : ℝ} (ht : 0 ≤ t) :
    lerayH (m + 1) (duhUp m G t) = duhUp m (fun r => lerayH m (G r)) t := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn
    (hG.norm.continuousOn)
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hM' : ∀ s ∈ Icc 0 t, ‖G s‖ ≤ max M 0 := fun s hs =>
    (by simpa using hM s hs : ‖G s‖ ≤ M).trans (le_max_left _ _)
  have hint := intervalIntegrable_upI hG ht hM0 hM'
  unfold duhUp
  rw [← (lerayH (m + 1)).intervalIntegral_comp_comm hint]
  simp only [lerayH_upI]

lemma lerayH_duhν {m : ℕ} {ν : ℝ} (hν : 0 < ν) {G : ℝ → Hm m} (hG : Continuous G)
    {t : ℝ} (ht : 0 ≤ t) :
    lerayH (m + 1) (duhν m ν G t) = duhν m ν (fun r => lerayH m (G r)) t := by
  unfold duhν
  rw [lerayH_duhUp (continuous_scaleG hG) (mul_nonneg hν.le ht)]
  congr 1
  funext σ
  simp only [scaleG, map_smul]

lemma lerayH_eq_rec_of {a b : ℕ} (e : a = b) (A B : Hm a) (h : lerayH a A = B) :
    lerayH b (e ▸ A) = e ▸ B := by
  cases e; exact h

lemma lerayH_duhHigh {k : ℕ} (hk : 2 ≤ k) {ν : ℝ} (hν : 0 < ν)
    {G : ℝ → Hm ((k + 1) - 1)} (hG : Continuous G) {t : ℝ} (ht : 0 ≤ t) :
    lerayH (k + 1) (duhHigh hk ν G t) =
      duhHigh hk ν (fun r => lerayH ((k + 1) - 1) (G r)) t := by
  unfold duhHigh
  exact lerayH_eq_rec_of (pred_succ_eq hk) _ _ (lerayH_duhν hν hG ht)

/-! ## The Leray projector fixes every slice of a mild path -/

theorem lerayH_mildS {k : ℕ} (hk : 2 ≤ k) {T : ℝ} (hT : 0 ≤ T) {ν : ℝ} (hν : 0 < ν)
    {u₀ : Hm (k + 1)} (h0 : lerayH (k + 1) u₀ = u₀) {u : XTs k T}
    (hu : IsMildS hk hT ν u₀ u) (t : Icc (0 : ℝ) T) :
    lerayH (k + 1) (u t) = u t := by
  conv_rhs => rw [hu t]
  rw [hu t, map_sub, lerayH_heatH, h0,
    lerayH_duhHigh hk hν (continuous_NSN_extUS hk hT u) t.2.1]
  simp only [lerayH_NSN]

/-! ## Divergence-free data have Leray-fixed Fourier representatives -/

open FourierTransform FeffermanSchwartz FeffermanSobolev NavierStokes3D in
lemma fourier_proj {g : E3 → V} (hg : Integrable g) (i : Fin 3) (ξ : E3) :
    𝓕 (fun x => g x i) ξ = 𝓕 g ξ i := by
  rw [Real.fourier_eq, Real.fourier_eq]
  have hint := (Real.fourierIntegral_convergent_iff ξ).mpr hg
  have := (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin 3) i).integral_comp_comm hint
  refine Eq.trans ?_ this
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [Circle.smul_def]

open FourierTransform FeffermanSchwartz NavierStokes3D LineDeriv RepairedTether in
/-- Fourier side of `div u₀ = 0`: `⟨ξ, 𝓕 u₀ (ξ)⟩ = 0` for every `ξ`. -/
theorem inner_fourier_eq_zero {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀)
    (hdec : FeffermanDecay u₀) (hdiv : ∀ x, div u₀ x = 0) (ξ : E3) :
    inner ℂ (ξc ξ) (𝓕 (cplx ∘ u₀) ξ) = 0 := by
  set f := toSchwartz u₀ hf hdec with hfdef
  have hfun : (f : E3 → V) = cplx ∘ u₀ := rfl
  -- Fourier transform of each partial derivative, read in coordinate `i`.
  have hpart : ∀ i : Fin 3,
      𝓕 (fun x : E3 => ((∂_{EuclideanSpace.single i (1 : ℝ)} f) x i : ℂ)) ξ =
        (2 * π * Complex.I) * ((ξ i : ℝ) : ℂ) * 𝓕 (cplx ∘ u₀) ξ i := by
    intro i
    rw [fourier_proj (∂_{EuclideanSpace.single i (1 : ℝ)} f).integrable i ξ,
      ← SchwartzMap.fourier_coe, SchwartzMap.fourier_lineDerivOp_eq]
    have hg : (fun x : E3 => inner ℝ x (EuclideanSpace.single i (1 : ℝ))).HasTemperateGrowth :=
      ((innerSL ℝ).flip (EuclideanSpace.single i (1 : ℝ))).hasTemperateGrowth
    rw [SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hg,
      SchwartzMap.fourier_coe, hfun]
    have hin : inner ℝ ξ (EuclideanSpace.single i (1 : ℝ)) = ξ i := by
      have := EuclideanSpace.inner_single_right (𝕜 := ℝ) i (1 : ℝ) ξ
      simpa using this
    rw [hin]
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [mul_assoc (2 * π * Complex.I)]
    congr 1
  -- The physical sum of the diagonal partials is `div u₀ = 0`.
  have hdiff : Differentiable ℝ u₀ := hf.differentiable (by simp)
  have hsum : ∀ x : E3,
      (∑ i : Fin 3, (∂_{EuclideanSpace.single i (1 : ℝ)} f) x i) = 0 := by
    intro x
    have hcomp : fderiv ℝ (cplx ∘ u₀) x = cplx.comp (fderiv ℝ u₀ x) :=
      (cplx.hasFDerivAt.comp x (hdiff x).hasFDerivAt).fderiv
    have hcoord : ∀ i : Fin 3, fderiv ℝ (fun y => u₀ y i) x =
        (EuclideanSpace.proj (𝕜 := ℝ) i).comp (fderiv ℝ u₀ x) := fun i =>
      ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x (hdiff x).hasFDerivAt).fderiv
    have h0 := hdiv x
    unfold div at h0
    simp only [hcoord] at h0
    have : (∑ i : Fin 3, (∂_{EuclideanSpace.single i (1 : ℝ)} f) x i) =
        ((∑ i : Fin 3, (EuclideanSpace.proj (𝕜 := ℝ) i).comp (fderiv ℝ u₀ x)
          (EuclideanSpace.single i 1) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, hfun, hcomp]
      rfl
    rw [this, h0, Complex.ofReal_zero]
  -- Sum the Fourier identities.
  have hint : ∀ i : Fin 3, Integrable
      (fun x : E3 => ((∂_{EuclideanSpace.single i (1 : ℝ)} f) x i : ℂ)) := fun i =>
    (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin 3) i).integrable_comp
      (∂_{EuclideanSpace.single i (1 : ℝ)} f).integrable
  have htot : (∑ i : Fin 3,
      𝓕 (fun x : E3 => ((∂_{EuclideanSpace.single i (1 : ℝ)} f) x i : ℂ)) ξ) = 0 := by
    have hlin : (∑ i : Fin 3,
        𝓕 (fun x : E3 => ((∂_{EuclideanSpace.single i (1 : ℝ)} f) x i : ℂ)) ξ) =
        𝓕 (fun x : E3 => (∑ i : Fin 3, (∂_{EuclideanSpace.single i (1 : ℝ)} f) x i : ℂ)) ξ := by
      simp only [Real.fourier_eq, Finset.smul_sum]
      rw [integral_finset_sum _ fun i _ => (Real.fourierIntegral_convergent_iff ξ).mpr (hint i)]
    rw [hlin]
    simp only [hsum]
    simp [Real.fourier_eq]
  simp only [hpart] at htot
  have hinner : inner ℂ (ξc ξ) (𝓕 (cplx ∘ u₀) ξ) =
      ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) * 𝓕 (cplx ∘ u₀) ξ i := by
    simp [PiLp.inner_apply, ξc, mul_comm]
  rw [hinner]
  have h2 : (2 * π * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have : (2 * π * Complex.I) * ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) * 𝓕 (cplx ∘ u₀) ξ i = 0 := by
    rw [Finset.mul_sum]
    simpa [mul_assoc] using htot
  exact (mul_eq_zero.mp this).resolve_left h2

open FourierTransform FeffermanSobolev RepairedTether in
/-- The Fourier representative of divergence-free Fefferman data is fixed by `lerayH`. -/
theorem lerayH_toHmFeff {u₀ : NavierStokes3D.VelocityField} (hf : ContDiff ℝ ∞ u₀)
    (hdec : FeffermanDecay u₀) (hdiv : ∀ x, NavierStokes3D.div u₀ x = 0) (m : ℕ) :
    lerayH m (toHmFeff u₀ hf hdec m) = toHmFeff u₀ hf hdec m := by
  refine Lp.ext ?_
  have h2 := coeFn_toHm (fourierEnergy_lt_top_of_feffermanDecay hf hdec m)
  have h3 := (ac_μw m).ae_le (coeFn_fourier_toL2 hf hdec)
  filter_upwards [coeFn_lerayH m (toHmFeff u₀ hf hdec m), h2, h3] with ξ e1 e2 e3
  unfold toHmFeff at e1 ⊢
  rw [e1, e2, e3]
  exact lerSym_fix (inner_fourier_eq_zero hf hdec hdiv ξ)

/-! ## Physical divergence of a Leray-fixed representative -/

open FourierTransform in
lemma fourierInv_proj {g : E3 → V} (hg : Integrable g) (i : Fin 3) (x : E3) :
    𝓕⁻ (fun ξ => g ξ i) x = 𝓕⁻ g x i := by
  rw [fourierInv_eq_fourier_neg, fourierInv_eq_fourier_neg]
  exact fourier_proj hg i (-x)

open FourierTransform in
lemma fourierInv_finset_sum {h : Fin 3 → E3 → ℂ} (hh : ∀ i, Integrable (h i)) (x : E3) :
    (∑ i : Fin 3, 𝓕⁻ (h i) x) = 𝓕⁻ (fun ξ => ∑ i : Fin 3, h i ξ) x := by
  simp only [fourierInv_eq_fourier_neg, Real.fourier_eq, Finset.smul_sum]
  rw [integral_finset_sum _ fun i _ => (Real.fourierIntegral_convergent_iff (-x)).mpr (hh i)]

open FourierTransform FourierInvFDeriv FourierInvBCF InverseSobolev InclNSN in
/-- If `lerayH m G = G` (`m ≥ 3`), the physical field of `G` is divergence-free. -/
theorem div_physicalOfHm_of_lerayH {m : ℕ} (hm : 3 ≤ m) {G : Hm m}
    (hG : lerayH m G = G) (x : E3) :
    NavierStokes3D.div (physicalOfHm G) x = 0 := by
  have hm2 := FourierInvFDeriv.two_le_of_three hm
  let L : Fin 3 → V →L[ℝ] ℝ := fun i => (EuclideanSpace.proj (𝕜 := ℝ) i).comp realifyCLM
  have hcoord : ∀ i : Fin 3, (fun y => physicalOfHm G y i) =
      fun y => L i ((fourierInvBCF hm2 G).toFun y) := fun i => rfl
  have hterm : ∀ i : Fin 3,
      (fderiv ℝ (fun y => physicalOfHm G y i) x) (EuclideanSpace.single i 1) =
        (𝓕⁻ (fun ξ => (dH (one_le_of_three hm) i G : E3 → V) ξ i) x).re := by
    intro i
    have hd : HasFDerivAt (fun y => L i ((fourierInvBCF hm2 G).toFun y))
        ((L i).comp (spatFDeriv hm G x)) x :=
      (L i).hasFDerivAt.comp x (hasFDerivAt_fourierInvBCF hm G x)
    rw [hcoord i, hd.fderiv,
      ContinuousLinearMap.comp_apply, spatFDeriv_apply,
      fourierInv_proj (integrable_of_Hm (two_le_pred_of_three hm) _) i x]
    have hsum : (∑ j : Fin 3, (EuclideanSpace.single i (1 : ℝ) : E3) j •
        fourierInvBCF (two_le_pred_of_three hm) (dH (one_le_of_three hm) j G) x) =
        fourierInvBCF (two_le_pred_of_three hm) (dH (one_le_of_three hm) i G) x := by
      rw [Finset.sum_eq_single i]
      · rw [PiLp.single_apply, if_pos rfl]
        exact one_smul ℝ _
      · intro j _ hj
        rw [PiLp.single_apply, if_neg hj]
        exact zero_smul ℝ _
      · simp
    rw [hsum]
    rfl
  unfold NavierStokes3D.div
  simp only [hterm]
  rw [← Complex.re_sum,
    fourierInv_finset_sum (h := fun i ξ => (dH (one_le_of_three hm) i G : E3 → V) ξ i) (fun i => (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin 3) i).integrable_comp
      (integrable_of_Hm (two_le_pred_of_three hm) (dH (one_le_of_three hm) i G))) x]
  have hzero : (fun ξ => ∑ i : Fin 3, (dH (one_le_of_three hm) i G : E3 → V) ξ i)
      =ᵐ[volume] fun _ => (0 : ℂ) := by
    have hd : ∀ i : Fin 3, (dH (one_le_of_three hm) i G : E3 → V) =ᵐ[volume]
        fun ξ => Nonlinear.derivSym i ξ ((G : E3 → V) ξ) := fun i =>
      (ac_vol (m - 1)).ae_le (coeFn_dH (one_le_of_three hm) i G)
    have hl : (G : E3 → V) =ᵐ[volume] fun ξ => lerSym ξ ((G : E3 → V) ξ) := by
      have := (ac_vol m).ae_le (coeFn_lerayH m G)
      rw [hG] at this
      exact this
    filter_upwards [hd 0, hd 1, hd 2, hl] with ξ h0 h1 h2 hlξ
    have hperp := lerSym_perp ξ ((G : E3 → V) ξ)
    rw [← hlξ] at hperp
    have hpts : ∀ i : Fin 3, (dH (one_le_of_three hm) i G : E3 → V) ξ =
        Nonlinear.derivSym i ξ ((G : E3 → V) ξ) := by
      intro i; fin_cases i <;> simp [h0, h1, h2]
    simp only [hpts, Nonlinear.derivSym_apply, SobolevFourier.sym, PiLp.smul_apply,
      smul_eq_mul]
    have hinner : inner ℂ (ξc ξ) ((G : E3 → V) ξ) =
        ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) * (G : E3 → V) ξ i := by
      simp [PiLp.inner_apply, ξc, mul_comm]
    rw [hinner] at hperp
    calc (∑ i : Fin 3, 2 * (π : ℂ) * Complex.I * ((ξ i : ℝ) : ℂ) * (G : E3 → V) ξ i)
        = 2 * (π : ℂ) * Complex.I *
            ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) * (G : E3 → V) ξ i := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by rw [hperp, mul_zero]
  rw [fourierInv_eq_fourier_neg, Real.fourier_eq]
  have hz : (fun ξ : E3 => Real.fourierChar (-inner ℝ ξ (-x)) •
      ∑ i : Fin 3, (dH (one_le_of_three hm) i G : E3 → V) ξ i) =ᵐ[volume] fun _ => (0 : ℂ) :=
    hzero.mono fun ξ hξ => by simp only at hξ ⊢; rw [hξ, smul_zero]
  rw [integral_congr_ae hz, integral_zero, Complex.zero_re]

/-! ## Item 3(C): the realized mild field is divergence-free -/

open RepairedTether in
/-- **The mild path stays divergence-free.** For divergence-free Fefferman data,
the realized mild field `physicalMild` satisfies `div u(t) = 0` on all of `ℝ³`
at every time `t` (outside `[0, T]` the path is the constant endpoint
extension, so the identity holds for every `t : ℝ`). -/
theorem div_physicalMild {u₀ : NavierStokes3D.VelocityField} (hf : ContDiff ℝ ∞ u₀)
    (hdec : FeffermanDecay u₀) (hdiv : ∀ x, NavierStokes3D.div u₀ x = 0)
    {ν : ℝ} (hν : 0 < ν) (t : ℝ) (x : E3) :
    NavierStokes3D.div (physicalMild hf hdec hν t) x = 0 := by
  have hT := Tfeff_nonneg hf hdec hν
  set p := persistPath hf hdec hν (by norm_num : 2 ≤ 2) with hp
  have hfix : ∀ s : Icc (0 : ℝ) (Tfeff hf hdec hν), lerayH 3 (p s) = p s :=
    lerayH_mildS (by norm_num : 2 ≤ 2) hT hν (lerayH_toHmFeff hf hdec hdiv 3)
      (persistPath_mildS hf hdec hν (by norm_num : 2 ≤ 2))
  have hext : ContinuousMap.IccExtend hT p t = p (projIcc 0 (Tfeff hf hdec hν) hT t) := by
    rw [ContinuousMap.coe_IccExtend]; rfl
  change NavierStokes3D.div (physicalOfHm (ContinuousMap.IccExtend hT p t)) x = 0
  rw [hext]
  exact div_physicalOfHm_of_lerayH (le_refl 3) (hfix _) x

#print axioms MildDivFree.lerayH_mildS
#print axioms MildDivFree.inner_fourier_eq_zero
#print axioms MildDivFree.lerayH_toHmFeff
#print axioms MildDivFree.div_physicalOfHm_of_lerayH
#print axioms MildDivFree.div_physicalMild

end MildDivFree
