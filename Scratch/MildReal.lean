import Scratch.MildDivFree
import Scratch.LerayPressure

/-! # The realized mild field is real

`refl G (ξ) = conj (G (-ξ))` is a real-linear isometry of every `Ĥ^m`.  It
commutes with the heat, Leray, derivative and Laplacian multipliers, with the
Fourier-side products, and with the smoothing Duhamel integral, and it fixes
the representative of real Fefferman data.  So `refl ∘ u` is again a mild
solution in the working ball; uniqueness gives `refl (u t) = u t`, and the
inverse Fourier transform of a `refl`-fixed representative is real. -/

open MeasureTheory Real Filter Topology Set
open scoped ENNReal ContDiff ComplexConjugate

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
namespace MildReal

open LerayHeat SobolevFourier SobolevHilbert HeatSobolev Duhamel DuhamelUp
  MildExistence PersistenceHm FeffermanMild

/-! ## Coordinatewise conjugation on `ℂ³` -/

def vconjFun (v : V) : V := WithLp.toLp 2 (fun i => conj (v i))

@[simp] lemma vconjFun_apply (v : V) (i : Fin 3) : vconjFun v i = conj (v i) := rfl

lemma vconjFun_vconjFun (v : V) : vconjFun (vconjFun v) = v := by
  ext i; simp

lemma vconjFun_csmul (c : ℂ) (v : V) : vconjFun (c • v) = conj c • vconjFun v := by
  ext i; simp

lemma norm_vconjFun (v : V) : ‖vconjFun v‖ = ‖v‖ := by
  simp [EuclideanSpace.norm_eq]

/-- Coordinatewise conjugation, as a real-linear isometric involution of `ℂ³`. -/
def vconj : V ≃ₗᵢ[ℝ] V where
  toFun := vconjFun
  invFun := vconjFun
  map_add' v w := by ext i; simp
  map_smul' c v := by
    change vconjFun (c • v) = c • vconjFun v
    rw [NonlinearSmooth.real_smul_eq_coe_smul_V, NonlinearSmooth.real_smul_eq_coe_smul_V,
      vconjFun_csmul, Complex.conj_ofReal]
  left_inv v := vconjFun_vconjFun v
  right_inv v := vconjFun_vconjFun v
  norm_map' v := norm_vconjFun v

@[simp] lemma vconj_apply (v : V) (i : Fin 3) : vconj v i = conj (v i) := rfl

lemma vconj_vconj (v : V) : vconj (vconj v) = v := vconjFun_vconjFun v

lemma vconj_csmul (c : ℂ) (v : V) : vconj (c • v) = conj c • vconj v := by
  ext i; simp

lemma vconj_sub (v w : V) : vconj (v - w) = vconj v - vconj w := map_sub vconj v w

lemma enorm_vconj (v : V) : ‖vconj v‖ₑ = ‖v‖ₑ := by
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, LinearIsometryEquiv.norm_map]

/-! ## The weight is even; `neg` transports `μw`-a.e. statements -/

lemma sobW_neg (m : ℕ) (ξ : E3) : sobW m (-ξ) = sobW m ξ := by
  rw [sobW_eq_Sp, sobW_eq_Sp, norm_neg]

lemma lintegral_μw_comp_neg (m : ℕ) (f : E3 → ℝ≥0∞) :
    ∫⁻ ξ, f (-ξ) ∂(μw m) = ∫⁻ ξ, f ξ ∂(μw m) := by
  rw [lintegral_μw, lintegral_μw]
  have h := (Measure.measurePreserving_neg (volume : Measure E3)).lintegral_comp_emb
    (MeasurableEquiv.neg E3).measurableEmbedding (fun ξ => sobW m ξ * f ξ)
  simp only [sobW_neg] at h
  exact h

lemma ae_neg {m : ℕ} {p : E3 → Prop} (h : ∀ᵐ ξ ∂(μw m), p ξ) :
    ∀ᵐ ξ ∂(μw m), p (-ξ) := by
  have hv : ∀ᵐ ξ ∂(volume : Measure E3), p ξ := (ac_vol m).ae_le h
  have : ∀ᵐ ξ ∂(volume : Measure E3), p (-ξ) :=
    (Measure.measurePreserving_neg (volume : Measure E3)).quasiMeasurePreserving.ae hv
  exact (ac_μw m).ae_le this

/-! ## The reflection `refl G (ξ) = conj (G (-ξ))` -/

def reflFun {m : ℕ} (G : Hm m) : E3 → V := fun ξ => vconj ((G : E3 → V) (-ξ))

lemma lintegral_reflFun {m : ℕ} (G : Hm m) :
    ∫⁻ ξ, ‖reflFun G ξ‖ₑ ^ (2 : ℝ) ∂(μw m) = ∫⁻ ξ, ‖(G : E3 → V) ξ‖ₑ ^ (2 : ℝ) ∂(μw m) := by
  simp only [reflFun, enorm_vconj]
  exact lintegral_μw_comp_neg m (fun ξ => ‖(G : E3 → V) ξ‖ₑ ^ (2 : ℝ))

lemma eLpNorm_reflFun {m : ℕ} (G : Hm m) :
    eLpNorm (reflFun G) 2 (μw m) = eLpNorm (G : E3 → V) 2 (μw m) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat]
  rw [lintegral_reflFun]

lemma memLp_reflFun {m : ℕ} (G : Hm m) : MemLp (reflFun G) 2 (μw m) := by
  refine ⟨?_, ?_⟩
  · exact (vconj.continuous.comp_stronglyMeasurable
      ((Lp.stronglyMeasurable G).comp_measurable measurable_neg)).aestronglyMeasurable
  · rw [eLpNorm_reflFun]; exact Lp.eLpNorm_lt_top G

def reflV {m : ℕ} (G : Hm m) : Hm m := (memLp_reflFun G).toLp _

lemma coeFn_reflV {m : ℕ} (G : Hm m) : (reflV G : E3 → V) =ᵐ[μw m] reflFun G :=
  MemLp.coeFn_toLp (memLp_reflFun G)

lemma norm_reflV {m : ℕ} (G : Hm m) : ‖reflV G‖ = ‖G‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (coeFn_reflV G), eLpNorm_reflFun]

lemma reflV_add {m : ℕ} (G H : Hm m) : reflV (G + H) = reflV G + reflV H := by
  refine Lp.ext ?_
  filter_upwards [coeFn_reflV (G + H), ae_neg (Lp.coeFn_add G H),
    Lp.coeFn_add (reflV G) (reflV H), coeFn_reflV G, coeFn_reflV H] with ξ h1 h2 h3 h4 h5
  rw [h1, h3, Pi.add_apply, h4, h5]
  simp only [reflFun]
  rw [h2, Pi.add_apply, map_add]

lemma reflV_csmul {m : ℕ} (c : ℂ) (G : Hm m) : reflV (c • G) = conj c • reflV G := by
  refine Lp.ext ?_
  filter_upwards [coeFn_reflV (c • G), ae_neg (Lp.coeFn_smul c G),
    Lp.coeFn_smul (conj c) (reflV G), coeFn_reflV G] with ξ h1 h2 h3 h4
  rw [h1, h3, Pi.smul_apply, h4]
  simp only [reflFun]
  rw [h2, Pi.smul_apply, vconj_csmul]

lemma reflV_smul {m : ℕ} (c : ℝ) (G : Hm m) : reflV (c • G) = c • reflV G := by
  rw [NonlinearSmooth.real_smul_eq_coe_smul, reflV_csmul, Complex.conj_ofReal,
    ← NonlinearSmooth.real_smul_eq_coe_smul]

/-- `refl` as a real-linear contraction `Ĥ^m → Ĥ^m` (in fact an isometry). -/
def refl (m : ℕ) : Hm m →L[ℝ] Hm m :=
  LinearMap.mkContinuous ⟨⟨reflV, reflV_add⟩, reflV_smul⟩ 1
    (fun G => by simp [norm_reflV])

lemma refl_apply {m : ℕ} (G : Hm m) : refl m G = reflV G := rfl

lemma coeFn_refl {m : ℕ} (G : Hm m) : (refl m G : E3 → V) =ᵐ[μw m] reflFun G :=
  coeFn_reflV G

lemma norm_refl {m : ℕ} (G : Hm m) : ‖refl m G‖ = ‖G‖ := norm_reflV G

lemma refl_csmul {m : ℕ} (c : ℂ) (G : Hm m) : refl m (c • G) = conj c • refl m G :=
  reflV_csmul c G

/-! ## Multipliers commuting with the reflection -/

section WMulRefl

variable {m m' : ℕ} (T : E3 → V →L[ℂ] V)
  (hT : ∀ g : E3 → V, AEStronglyMeasurable g → AEStronglyMeasurable (fun ξ => T ξ (g ξ)))
  (K : ℝ) (hK : 0 ≤ K) (hb : ∀ ξ, sobW m' ξ * ‖T ξ‖ₑ ^ 2 ≤ ENNReal.ofReal K * sobW m ξ)

theorem refl_wmul (hTc : ∀ ξ v, vconj (T (-ξ) v) = T ξ (vconj v)) (G : Hm m) :
    refl m' (wmul T hT K hK hb G) = wmul T hT K hK hb (refl m G) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_refl (wmul T hT K hK hb G), ae_neg (coeFn_wmul T hT K hK hb G),
    coeFn_wmul T hT K hK hb (refl m G), (ac_ww m m').ae_le (coeFn_refl G)]
    with ξ h1 h2 h3 h4
  rw [h1, h3, h4]
  simp only [reflFun]
  rw [h2]
  exact hTc ξ _

end WMulRefl

/-! ## The symbols are reflection-compatible -/

lemma gauss_neg (τ : ℝ) (ξ : E3) : gauss τ (-ξ) = gauss τ ξ := by
  simp [gauss, norm_neg]

lemma heatSym_refl (τ : ℝ) (ξ : E3) (v : V) :
    vconj (heatSym τ (-ξ) v) = heatSym τ ξ (vconj v) := by
  rw [heatSym_apply, heatSym_apply, vconj_csmul, gauss_neg, Complex.conj_ofReal]

lemma ξc_neg (ξ : E3) : ξc (-ξ) = -ξc ξ := by
  ext i; simp [ξc]

lemma vconj_ξc (ξ : E3) : vconj (ξc ξ) = ξc ξ := by
  ext i; simp [ξc]

lemma inner_ξc_vconj (ξ : E3) (v : V) :
    inner ℂ (ξc ξ) (vconj v) = conj (inner ℂ (ξc ξ) v) := by
  simp [PiLp.inner_apply, ξc, map_sum]

lemma lerSym_refl (ξ : E3) (v : V) :
    vconj (lerSym (-ξ) v) = lerSym ξ (vconj v) := by
  rw [lerSym_apply, lerSym_apply, vconj_sub, vconj_csmul, ξc_neg, norm_neg, inner_neg_left,
    inner_ξc_vconj, map_neg, vconj_ξc, map_div₀, Complex.conj_ofReal, map_neg, smul_neg,
    neg_div, neg_smul, neg_neg]

lemma derivSym_refl (j : Fin 3) (ξ : E3) (v : V) :
    vconj (Nonlinear.derivSym j (-ξ) v) = Nonlinear.derivSym j ξ (vconj v) := by
  rw [Nonlinear.derivSym_apply, Nonlinear.derivSym_apply, vconj_csmul]
  congr 1
  simp [SobolevFourier.sym, Complex.conj_ofReal]
  left; exact Complex.conj_ofNat 2

lemma id_refl (ξ : E3) (v : V) :
    vconj ((fun _ : E3 => ContinuousLinearMap.id ℂ V) (-ξ) v) =
      (fun _ : E3 => ContinuousLinearMap.id ℂ V) ξ (vconj v) := rfl

lemma refl_heatH (m : ℕ) (τ : ℝ) (G : Hm m) :
    refl m (heatH m τ G) = heatH m τ (refl m G) :=
  refl_wmul _ _ _ _ _ (heatSym_refl τ) G

lemma refl_heatUp (m : ℕ) {τ : ℝ} (hτ : 0 < τ) (G : Hm m) :
    refl (m + 1) (heatUp m hτ G) = heatUp m hτ (refl m G) :=
  refl_wmul _ _ _ _ _ (heatSym_refl τ) G

lemma refl_lerayH (m : ℕ) (G : Hm m) :
    refl m (lerayH m G) = lerayH m (refl m G) :=
  refl_wmul _ _ _ _ _ lerSym_refl G

lemma refl_incl {m m' : ℕ} (h : m' ≤ m) (G : Hm m) :
    refl m' (incl h G) = incl h (refl m G) :=
  refl_wmul _ _ _ _ _ id_refl G

lemma refl_dH3 (j : Fin 3) (G : Hm 3) :
    refl 2 (Nonlinear.dH j G) = Nonlinear.dH j (refl 3 G) :=
  refl_wmul _ _ _ _ _ (derivSym_refl j) G

lemma refl_dH {s : ℕ} (hs : 1 ≤ s) (j : Fin 3) (G : Hm s) :
    refl (s - 1) (NonlinearHm.dH hs j G) = NonlinearHm.dH hs j (refl s G) :=
  refl_wmul _ _ _ _ _ (derivSym_refl j) G

/-! ## Products -/

open scoped Convolution in
lemma vconj_conv (L : V →L[ℂ] V →L[ℂ] V)
    (hL : ∀ a b, vconj (L a b) = L (vconj a) (vconj b)) (f g : E3 → V) (ξ : E3) :
    vconj ((f ⋆[L] g) (-ξ)) =
      ((fun η => vconj (f (-η))) ⋆[L] (fun η => vconj (g (-η)))) ξ := by
  rw [convolution_def, convolution_def]
  have hc : vconj (∫ t, L (f t) (g (-ξ - t))) = ∫ t, vconj (L (f t) (g (-ξ - t))) :=
    (vconj.toLinearIsometry.integral_comp_comm (fun t => L (f t) (g (-ξ - t)))).symm
  rw [hc]
  simp only [hL]
  rw [← integral_neg_eq_self]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [sub_neg_eq_add]
  congr 3
  abel

lemma Lij_refl (i j : Fin 3) (a b : V) :
    vconj (Nonlinear.Lij i j a b) = Nonlinear.Lij i j (vconj a) (vconj b) := by
  ext k
  simp only [Nonlinear.Lij_apply, Nonlinear.embedCLM_apply, vconj_apply]
  by_cases h : k = i
  · subst h; simp [Nonlinear.coordCLM]
  · simp [h]

lemma Lprod_refl (i j : Fin 3) (a b : V) :
    vconj (LerayPressure.Lprod i j a b) = LerayPressure.Lprod i j (vconj a) (vconj b) := by
  ext k
  simp only [LerayPressure.Lprod_apply, Nonlinear.embedCLM_apply, vconj_apply]
  by_cases h : k = 0
  · subst h; simp [Nonlinear.coordCLM]
  · simp [h]

open scoped Convolution in
lemma conv_refl_ae {m : ℕ} (L : V →L[ℂ] V →L[ℂ] V) (F G : Hm m) :
    ((refl m F : E3 → V) ⋆[L] (refl m G : E3 → V)) =
      ((fun η => vconj ((F : E3 → V) (-η))) ⋆[L] (fun η => vconj ((G : E3 → V) (-η)))) :=
  convolution_congr (L := L) ((ac_vol m).ae_le (coeFn_refl F)) ((ac_vol m).ae_le (coeFn_refl G))

theorem refl_mulF {s : ℕ} (hs : 3 ≤ s) (L : V →L[ℂ] V →L[ℂ] V)
    (hL : ∀ a b, vconj (L a b) = L (vconj a) (vconj b)) (F G : Hm s) :
    refl s (ProductHm.mulF L hs F G) = ProductHm.mulF L hs (refl s F) (refl s G) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_refl (ProductHm.mulF L hs F G), ae_neg (ProductHm.coeFn_mulF L hs F G),
    ProductHm.coeFn_mulF L hs (refl s F) (refl s G)] with ξ h1 h2 h3
  rw [h1, h3, conv_refl_ae]
  simp only [reflFun]
  rw [h2, vconj_conv L hL]

theorem refl_mulF3 (L : V →L[ℂ] V →L[ℂ] V)
    (hL : ∀ a b, vconj (L a b) = L (vconj a) (vconj b)) (F G : Hm 3) :
    refl 3 (ProductH3.mulF L F G) = ProductH3.mulF L (refl 3 F) (refl 3 G) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_refl (ProductH3.mulF L F G), ae_neg (ProductH3.coeFn_mulF L F G),
    ProductH3.coeFn_mulF L (refl 3 F) (refl 3 G)] with ξ h1 h2 h3
  rw [h1, h3, conv_refl_ae]
  simp only [reflFun]
  rw [h2, vconj_conv L hL]

theorem refl_NSN3 (u : Hm 3) : refl 2 (Nonlinear.NSN u) = Nonlinear.NSN (refl 3 u) := by
  unfold Nonlinear.NSN Nonlinear.divTensor
  rw [refl_lerayH, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [refl_dH3, refl_mulF3 _ (Lij_refl i j)]

theorem refl_NSN {s : ℕ} (hs : 3 ≤ s) (u : Hm s) :
    refl (s - 1) (NonlinearHm.NSN hs u) = NonlinearHm.NSN hs (refl s u) := by
  unfold NonlinearHm.NSN NonlinearHm.divTensor
  rw [refl_lerayH, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [refl_dH, refl_mulF hs _ (Lij_refl i j)]

/-! ## Duhamel integrals -/

lemma refl_upI {m : ℕ} (G : ℝ → Hm m) (t s : ℝ) :
    refl (m + 1) (upI G t s) = upI (fun r => refl m (G r)) t s := by
  unfold upI
  split_ifs with h
  · exact refl_heatUp m _ _
  · exact map_zero _

lemma refl_duhUp {m : ℕ} {G : ℝ → Hm m} (hG : Continuous G) {t : ℝ} (ht : 0 ≤ t) :
    refl (m + 1) (duhUp m G t) = duhUp m (fun r => refl m (G r)) t := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn
    (hG.norm.continuousOn)
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hM' : ∀ s ∈ Icc 0 t, ‖G s‖ ≤ max M 0 := fun s hs =>
    (by simpa using hM s hs : ‖G s‖ ≤ M).trans (le_max_left _ _)
  have hint := intervalIntegrable_upI hG ht hM0 hM'
  unfold duhUp
  rw [← (refl (m + 1)).intervalIntegral_comp_comm hint]
  simp only [refl_upI]

lemma refl_duhν {m : ℕ} {ν : ℝ} (hν : 0 < ν) {G : ℝ → Hm m} (hG : Continuous G)
    {t : ℝ} (ht : 0 ≤ t) :
    refl (m + 1) (duhν m ν G t) = duhν m ν (fun r => refl m (G r)) t := by
  unfold duhν
  rw [refl_duhUp (continuous_scaleG hG) (mul_nonneg hν.le ht)]
  congr 1
  funext σ
  simp only [scaleG, refl_csmul, Complex.conj_ofReal]

/-! ## Real data and real inverse Fourier transforms -/

open FourierTransform in
lemma vconj_circle_smul (a : ℝ) (v : V) :
    vconj (Real.fourierChar a • v) = Real.fourierChar (-a) • vconj v := by
  rw [Circle.smul_def, Circle.smul_def, vconj_csmul, ← Circle.coe_inv_eq_conj,
    ← AddChar.map_neg_eq_inv]

open FourierTransform in
lemma vconj_fourier_neg_of_real (f : E3 → E3) (ξ : E3) :
    vconj (𝓕 (cplx ∘ f) (-ξ)) = 𝓕 (cplx ∘ f) ξ := by
  rw [Real.fourier_eq, Real.fourier_eq]
  have hc := (vconj.toLinearIsometry.integral_comp_comm (μ := volume)
    (fun v : E3 => Real.fourierChar (-inner ℝ v (-ξ)) • (cplx ∘ f) v)).symm
  refine hc.trans (integral_congr_ae (Eventually.of_forall fun v => ?_))
  change vconj (Real.fourierChar (-inner ℝ v (-ξ)) • cplx (f v)) = _
  rw [vconj_circle_smul, inner_neg_right, neg_neg]
  congr 1
  ext i; simp [cplx_apply]

open FourierTransform FeffermanSobolev RepairedTether in
theorem refl_toHmFeff {u₀ : NavierStokes3D.VelocityField} (hf : ContDiff ℝ ∞ u₀)
    (hdec : FeffermanDecay u₀) (m : ℕ) :
    refl m (toHmFeff u₀ hf hdec m) = toHmFeff u₀ hf hdec m := by
  refine Lp.ext ?_
  have h2 := coeFn_toHm (fourierEnergy_lt_top_of_feffermanDecay hf hdec m)
  have h3 := (ac_μw m).ae_le (coeFn_fourier_toL2 hf hdec)
  filter_upwards [coeFn_refl (toHmFeff u₀ hf hdec m), ae_neg h2, ae_neg h3, h2, h3]
    with ξ e1 e2 e3 e4 e5
  unfold toHmFeff at e1 ⊢
  rw [e1, e4, e5]
  simp only [reflFun]
  rw [e2, e3]
  exact vconj_fourier_neg_of_real u₀ ξ

open FourierTransform InverseSobolev in
theorem vconj_fourierInv {m : ℕ} (G : Hm m) (x : E3) :
    vconj (𝓕⁻ (G : E3 → V) x) = 𝓕⁻ (refl m G : E3 → V) x := by
  rw [fourierInv_congr_ae ((ac_vol m).ae_le (coeFn_refl G)) x,
    fourierInv_eq_fourier_neg, fourierInv_eq_fourier_neg, Real.fourier_eq, Real.fourier_eq]
  have hc := (vconj.toLinearIsometry.integral_comp_comm (μ := volume)
    (fun v : E3 => Real.fourierChar (-inner ℝ v (-x)) • (G : E3 → V) v)).symm
  refine hc.trans ?_
  rw [← integral_neg_eq_self]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  change vconj (Real.fourierChar (-inner ℝ (-v) (-x)) • (G : E3 → V) (-v)) =
    Real.fourierChar (-inner ℝ v (-x)) • vconj ((G : E3 → V) (-v))
  rw [vconj_circle_smul, inner_neg_left, inner_neg_right]
  simp only [neg_neg]

/-- The inverse Fourier transform of a `refl`-fixed representative is real. -/
theorem fourierInv_im_eq_zero {m : ℕ} {G : Hm m} (hG : refl m G = G) (x : E3) (i : Fin 3) :
    (FourierTransformInv.fourierInv (G : E3 → V) x i).im = 0 := by
  have h := vconj_fourierInv G x
  rw [hG] at h
  have hi := congrArg (fun w : V => w i) h
  simp only [vconj_apply] at hi
  exact Complex.conj_eq_iff_im.mp hi

/-! ## The reflected mild path is again mild; uniqueness -/

/-- Reflection of a path in `C([0, T]; Ĥ³)`. -/
def reflPath {T : ℝ} (u : XT T) : XT T :=
  (ContinuousMap.mk (refl 3) (refl 3).continuous).comp u

lemma reflPath_apply {T : ℝ} (u : XT T) (t : Icc (0 : ℝ) T) : reflPath u t = refl 3 (u t) := rfl

lemma IccExtend_reflPath {T : ℝ} (hT : 0 ≤ T) (u : XT T) (s : ℝ) :
    ContinuousMap.IccExtend hT (reflPath u) s = refl 3 (ContinuousMap.IccExtend hT u s) := by
  rw [ContinuousMap.coe_IccExtend, ContinuousMap.coe_IccExtend]; rfl

lemma norm_reflPath_le {T : ℝ} (u : XT T) : ‖reflPath u‖ ≤ ‖u‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun t => by
    rw [reflPath_apply, norm_refl]; exact u.norm_coe_le_norm t

theorem isMild_reflPath {T : ℝ} (hT : 0 ≤ T) {ν : ℝ} (hν : 0 < ν) {u₀ : Hm 3}
    (h0 : refl 3 u₀ = u₀) {u : XT T} (hu : IsMild hT ν u₀ u) :
    IsMild hT ν u₀ (reflPath u) := by
  intro t
  rw [reflPath_apply, hu t, map_sub, refl_heatH, h0,
    refl_duhν hν (continuous_NSN_extU hT u) t.2.1]
  congr 2
  funext s
  rw [refl_NSN3, IccExtend_reflPath]

/-- Every slice of the `Ĥ³` shadow of the persisted mild path is `refl`-fixed. -/
theorem refl_persistPath {u₀ : NavierStokes3D.VelocityField} (hf : ContDiff ℝ ∞ u₀)
    (hdec : RepairedTether.FeffermanDecay u₀) {ν : ℝ} (hν : 0 < ν) {k : ℕ} (hk : 2 ≤ k)
    (t : Icc (0 : ℝ) (Tfeff hf hdec hν)) :
    refl 3 (inclMap hk (persistPath hf hdec hν hk) t) =
      inclMap hk (persistPath hf hdec hν hk) t := by
  have hT := Tfeff_nonneg hf hdec hν
  set P := inclMap hk (persistPath hf hdec hν hk)
  have hball := persistPath_memBall hf hdec hν hk
  have hball' : reflPath P ∈ Metric.closedBall (0 : XT (Tfeff hf hdec hν))
      (rad (FeffermanSobolev.toHmFeff u₀ hf hdec 3)) := by
    rw [mem_closedBall_zero_iff] at hball ⊢
    exact (norm_reflPath_le P).trans hball
  have hM := persistPath_mild3 hf hdec hν hk
  have hM' := isMild_reflPath hT hν (refl_toHmFeff hf hdec 3) hM
  have heq := unique_mild_in_ball hν hT (FeffermanSobolev.toHmFeff u₀ hf hdec 3) (Tfeff_visc hf hdec hν)
    hball' hball hM' hM
  exact congrArg (fun w : XT (Tfeff hf hdec hν) => w t) heq

/-- Every slice of every persisted path is `refl`-fixed. -/
theorem refl_persistPath_high {u₀ : NavierStokes3D.VelocityField} (hf : ContDiff ℝ ∞ u₀)
    (hdec : RepairedTether.FeffermanDecay u₀) {ν : ℝ} (hν : 0 < ν) {k : ℕ} (hk : 2 ≤ k)
    (t : Icc (0 : ℝ) (Tfeff hf hdec hν)) :
    refl (k + 1) (persistPath hf hdec hν hk t) = persistPath hf hdec hν hk t := by
  have h := refl_persistPath hf hdec hν hk t
  change refl 3 (incl (three_le_succ hk) (persistPath hf hdec hν hk t)) =
    incl (three_le_succ hk) (persistPath hf hdec hν hk t) at h
  rw [refl_incl] at h
  exact incl_injective (three_le_succ hk) h

/-! ## Item 3(D), reality: the complex inverse Fourier transform is the physical field -/

open FourierTransform in
/-- **The mild field is real.** For every `k ≥ 2` and `t ∈ [0, T]`, the complex
inverse Fourier transform of the persisted `Ĥ^{k+1}` slice equals the
complexification of the realized physical field. -/
theorem cplx_physicalMild {u₀ : NavierStokes3D.VelocityField} (hf : ContDiff ℝ ∞ u₀)
    (hdec : RepairedTether.FeffermanDecay u₀) {ν : ℝ} (hν : 0 < ν) {k : ℕ} (hk : 2 ≤ k)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (Tfeff hf hdec hν)) (x : E3) :
    cplx (physicalMild hf hdec hν t x) =
      𝓕⁻ ((persistPath hf hdec hν hk ⟨t, ht⟩ : Hm (k + 1)) : E3 → V) x := by
  rw [physicalMild_eq_path hf hdec hν hk ht]
  exact cplx_realify_of_real fun i =>
    fourierInv_im_eq_zero (refl_persistPath_high hf hdec hν hk ⟨t, ht⟩) x i

#print axioms MildReal.refl_wmul
#print axioms MildReal.refl_mulF
#print axioms MildReal.refl_NSN3
#print axioms MildReal.refl_NSN
#print axioms MildReal.refl_toHmFeff
#print axioms MildReal.vconj_fourierInv
#print axioms MildReal.isMild_reflPath
#print axioms MildReal.refl_persistPath
#print axioms MildReal.refl_persistPath_high
#print axioms MildReal.cplx_physicalMild

end MildReal
