import Scratch.MildReal
import Scratch.MildPathSmooth

/-! # The momentum equation for the realized mild field

Physical identification of the Fourier-side Navier–Stokes nonlinearity:
`𝓕⁻ (F ⋆[B] G) = B (𝓕⁻ F) (𝓕⁻ G)` for integrable representatives, the
convective term and the Leray pressure gradient of a real, divergence-free
`Ĥ^s` slice, and the resulting pointwise momentum equation. -/

open MeasureTheory Real Filter Topology Set FourierTransform
open scoped ENNReal ContDiff Convolution

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
namespace MildMomentum

open LerayHeat SobolevFourier SobolevHilbert MildExistence PersistenceHm FeffermanMild

/-! ## Convolution theorem for integrable (not necessarily continuous) functions -/

theorem fourier_conv_eq (B : V →L[ℂ] V →L[ℂ] V) {f g : E3 → V}
    (hf : Integrable f) (hg : Integrable g) (w : E3) :
    𝓕 (f ⋆[B] g) w = B (𝓕 f w) (𝓕 g w) := by
  set e : E3 → ℂ := fun v => ((Real.fourierChar (-inner ℝ v w) : Circle) : ℂ) with he
  have he_add : ∀ a b, e (a + b) = e a * e b := by
    intro a b
    simp only [he]
    rw [inner_add_left, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
  have he_norm : ∀ a, ‖e a‖ = 1 := fun a => Circle.norm_coe _
  have he_cont : Continuous e :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp
      ((continuous_id.inner continuous_const).neg))
  have hsm : ∀ (h : E3 → V) (v : E3),
      Real.fourierChar (-inner ℝ v w) • h v = e v • h v := fun h v => Circle.smul_def _ _
  rw [Real.fourier_eq, Real.fourier_eq, Real.fourier_eq]
  simp only [hsm]
  have hint : Integrable (fun p : E3 × E3 => B (f p.2) (g (p.1 - p.2)))
      ((volume : Measure E3).prod volume) := hf.convolution_integrand B hg
  have hint' : Integrable (Function.uncurry fun v t => e v • B (f t) (g (v - t)))
      ((volume : Measure E3).prod volume) := by
    refine hint.mono ((he_cont.comp continuous_fst).aestronglyMeasurable.smul
      hint.aestronglyMeasurable) (Eventually.of_forall fun p => ?_)
    change ‖e p.1 • B (f p.2) (g (p.1 - p.2))‖ ≤ ‖B (f p.2) (g (p.1 - p.2))‖
    rw [norm_smul, he_norm, one_mul]
  have hfe : Integrable (fun t => e t • f t) :=
    hf.mono (he_cont.aestronglyMeasurable.smul hf.aestronglyMeasurable)
      (Eventually.of_forall fun t => by rw [norm_smul, he_norm, one_mul])
  have hge : Integrable (fun t => e t • g t) :=
    hg.mono (he_cont.aestronglyMeasurable.smul hg.aestronglyMeasurable)
      (Eventually.of_forall fun t => by rw [norm_smul, he_norm, one_mul])
  calc ∫ v, e v • (f ⋆[B] g) v
      = ∫ v, ∫ t, e v • B (f t) (g (v - t)) := by
        refine integral_congr_ae (Eventually.of_forall fun v => ?_)
        simp only [convolution_def]
        exact (integral_smul (e v) _).symm
    _ = ∫ t, ∫ v, e v • B (f t) (g (v - t)) := integral_integral_swap hint'
    _ = ∫ t, ∫ v, B (e t • f t) (e v • g v) := by
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        dsimp only
        rw [← integral_add_right_eq_self _ t]
        refine integral_congr_ae (Eventually.of_forall fun v => ?_)
        simp only [add_sub_cancel_right, he_add, map_smul, ContinuousLinearMap.smul_apply,
          smul_smul]
    _ = ∫ t, B (e t • f t) (∫ v, e v • g v) := by
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        exact (B (e t • f t)).integral_comp_comm hge
    _ = B (∫ t, e t • f t) (∫ v, e v • g v) :=
        (B.flip (∫ v, e v • g v)).integral_comp_comm hfe

/-! ## Inverse Fourier transform of an `Ĥ^s` product -/

open InverseSobolev in
theorem fourierInv_mulF {s : ℕ} (hs : 3 ≤ s) (B : V →L[ℂ] V →L[ℂ] V) (F G : Hm s) (x : E3) :
    𝓕⁻ (ProductHm.mulF B hs F G : E3 → V) x = B (𝓕⁻ (F : E3 → V) x) (𝓕⁻ (G : E3 → V) x) := by
  have hF := ProductHm.integrable_of_Hm_ge3 hs F
  have hG := ProductHm.integrable_of_Hm_ge3 hs G
  rw [fourierInv_congr_ae ((ac_vol s).ae_le (ProductHm.coeFn_mulF B hs F G)) x]
  rw [fourierInv_eq_fourier_neg, fourier_conv_eq B hF hG, fourierInv_eq_fourier_neg,
    fourierInv_eq_fourier_neg]

/-! ## Evaluation of `𝓕⁻` is linear in the representative -/

open FourierInvFDeriv in
lemma fourierInv_eq_evMap {m : ℕ} (hm : 2 ≤ m) (H : Hm m) (x : E3) :
    𝓕⁻ (H : E3 → V) x = evMap hm x H := rfl

/-! ## Spatial derivatives of `𝓕⁻ G` -/

open FourierInvFDeriv FourierInvBCF InverseSobolev InclNSN NonlinearHm

lemma spatFDeriv_single {m : ℕ} (hm : 3 ≤ m) (G : Hm m) (x : E3) (j : Fin 3) :
    spatFDeriv hm G x (EuclideanSpace.single j 1) =
      𝓕⁻ (dH (one_le_of_three hm) j G : E3 → V) x := by
  rw [spatFDeriv_apply, Finset.sum_eq_single j]
  · rw [PiLp.single_apply, if_pos rfl]
    exact one_smul ℝ _
  · intro k _ hk
    rw [PiLp.single_apply, if_neg hk]
    exact zero_smul ℝ _
  · simp

lemma hasFDerivAt_fourierInv {m : ℕ} (hm : 3 ≤ m) (G : Hm m) (x : E3) :
    HasFDerivAt (fun y : E3 => 𝓕⁻ (G : E3 → V) y) (spatFDeriv hm G x) x :=
  hasFDerivAt_fourierInvBCF hm G x

lemma fderiv_fourierInv_single {m : ℕ} (hm : 3 ≤ m) (G : Hm m) (x : E3) (j : Fin 3) :
    fderiv ℝ (fun y : E3 => 𝓕⁻ (G : E3 → V) y) x (EuclideanSpace.single j 1) =
      𝓕⁻ (dH (one_le_of_three hm) j G : E3 → V) x := by
  rw [(hasFDerivAt_fourierInv hm G x).fderiv, spatFDeriv_single]

/-- Product rule on the Fourier side: `∂ⱼ (wᵢ wⱼ) eᵢ`. -/
lemma fourierInv_dH_mulF_Lij {s : ℕ} (hs : 3 ≤ s) (U : Hm s) (i j : Fin 3) (x : E3) :
    𝓕⁻ (dH (one_le_of_three hs) j (ProductHm.mulF (Nonlinear.Lij i j) hs U U) : E3 → V) x =
      Nonlinear.embedCLM i
        (𝓕⁻ (dH (one_le_of_three hs) j U : E3 → V) x i * 𝓕⁻ (U : E3 → V) x j +
          𝓕⁻ (U : E3 → V) x i * 𝓕⁻ (dH (one_le_of_three hs) j U : E3 → V) x j) := by
  set M := ProductHm.mulF (Nonlinear.Lij i j) hs U U
  have h1 := hasFDerivAt_fourierInv hs M x
  have hfun : (fun y : E3 => 𝓕⁻ (M : E3 → V) y) = fun y =>
      Nonlinear.embedCLM i (𝓕⁻ (U : E3 → V) y i * 𝓕⁻ (U : E3 → V) y j) := by
    funext y
    rw [fourierInv_mulF hs, Nonlinear.Lij_apply]
    rfl
  rw [hfun] at h1
  have hw := hasFDerivAt_fourierInv hs U x
  have hc : ∀ k : Fin 3, HasFDerivAt (fun y => 𝓕⁻ (U : E3 → V) y k)
      ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℂ) k).comp (spatFDeriv hs U x)) x :=
    fun k => (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℂ) k).hasFDerivAt.comp x hw
  have h2 := ((Nonlinear.embedCLM i).restrictScalars ℝ).hasFDerivAt.comp x
    ((hc i).mul (hc j))
  have huniq := h1.unique h2
  rw [← spatFDeriv_single hs M x j, huniq]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars']
  congr 1
  refine (show _ = 𝓕⁻ (U : E3 → V) x i * spatFDeriv hs U x (EuclideanSpace.single j 1) j +
      𝓕⁻ (U : E3 → V) x j * spatFDeriv hs U x (EuclideanSpace.single j 1) i from rfl).trans ?_
  rw [spatFDeriv_single]
  ring

/-- Complex divergence of a Leray-fixed slice: `∑ᵢ (𝓕⁻ (∂ᵢ G))ᵢ = 0`. -/
lemma sum_fourierInv_dH_self {m : ℕ} (hm : 3 ≤ m) {G : Hm m}
    (hG : lerayH m G = G) (x : E3) :
    ∑ i : Fin 3, 𝓕⁻ (dH (one_le_of_three hm) i G : E3 → V) x i = 0 := by
  simp only [← MildDivFree.fourierInv_proj (integrable_of_Hm (two_le_pred_of_three hm) _) _ x]
  rw [MildDivFree.fourierInv_finset_sum
      (h := fun i ξ => (dH (one_le_of_three hm) i G : E3 → V) ξ i)
      (fun i => (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin 3) i).integrable_comp
        (integrable_of_Hm (two_le_pred_of_three hm) (dH (one_le_of_three hm) i G))) x]
  have hzero : (fun ξ => ∑ i : Fin 3, (dH (one_le_of_three hm) i G : E3 → V) ξ i)
      =ᵐ[volume] fun _ => (0 : ℂ) := by
    have hd : ∀ i : Fin 3, (dH (one_le_of_three hm) i G : E3 → V) =ᵐ[volume]
        fun ξ => Nonlinear.derivSym i ξ ((G : E3 → V) ξ) := fun i =>
      (ac_vol (m - 1)).ae_le (coeFn_dH (one_le_of_three hm) i G)
    have hl : (G : E3 → V) =ᵐ[volume] fun ξ => lerSym ξ ((G : E3 → V) ξ) := by
      have := (ac_vol m).ae_le (MildDivFree.coeFn_lerayH m G)
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
  rw [integral_congr_ae hz, integral_zero]

lemma fourierInv_divTensor {s : ℕ} (hs : 3 ≤ s) (U : Hm s) (x : E3) :
    𝓕⁻ (divTensor hs U : E3 → V) x = ∑ i : Fin 3, ∑ j : Fin 3,
      𝓕⁻ (dH (one_le_of_three hs) j (ProductHm.mulF (Nonlinear.Lij i j) hs U U) : E3 → V) x := by
  simp only [fourierInv_eq_evMap (two_le_pred_of_three hs), divTensor, map_sum]

open NavierStokes3D in
/-- **Convective term.** For a real, Leray-fixed slice `U ∈ Ĥ^s` (`s ≥ 3`), the
physical field of `∇·(U ⊗ U)` is `(u·∇)u` with `u = physicalOfHm U`. -/
theorem realify_fourierInv_divTensor {s : ℕ} (hs : 3 ≤ s) {U : Hm s}
    (hdiv : lerayH s U = U) (hreal : ∀ y : E3, ∀ k : Fin 3, (𝓕⁻ (U : E3 → V) y k).im = 0)
    (x : E3) :
    realify (𝓕⁻ (divTensor hs U : E3 → V) x) =
      convective (physicalOfHm U) (physicalOfHm U) x := by
  set d : Fin 3 → V := fun j => 𝓕⁻ (dH (one_le_of_three hs) j U : E3 → V) x with hd
  set w : V := 𝓕⁻ (U : E3 → V) x with hw
  have hsum0 : ∑ j : Fin 3, d j j = 0 := sum_fourierInv_dH_self hs hdiv x
  have hderiv : HasFDerivAt (physicalOfHm U) (realifyCLM.comp (spatFDeriv hs U x)) x := by
    rw [physicalOfHm_eq_comp]
    exact realifyCLM.hasFDerivAt.comp x (hasFDerivAt_fourierInv hs U x)
  unfold convective
  rw [hderiv.fderiv, fourierInv_divTensor]
  simp only [fourierInv_dH_mulF_Lij]
  ext k
  rw [ContinuousLinearMap.comp_apply, realifyCLM_apply, spatFDeriv_apply]
  simp only [realify, PiLp.toLp_apply, ← hw]
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, Nonlinear.embedCLM_apply, PiLp.single_apply]
  have hL : ∀ A : Fin 3 → Fin 3 → ℂ,
      (∑ a : Fin 3, ∑ b : Fin 3, if k = a then A a b else 0) = ∑ b : Fin 3, A k b := by
    intro A
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hL (fun a b => 𝓕⁻ (dH (one_le_of_three hs) b U : E3 → V) x a * w b +
    w a * 𝓕⁻ (dH (one_le_of_three hs) b U : E3 → V) x b)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  change (∑ b, d b k * w b + w k * ∑ b, d b b).re = _
  rw [hsum0, mul_zero, add_zero, Complex.re_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  change (d c k * w c).re = ((realify w c) • d c k).re
  rw [Complex.mul_re, hw, hreal x c, mul_zero, sub_zero, ← hw]
  simp [realify, mul_comm]

/-! ## The Leray pressure gradient on the Fourier side -/

open LerayPressure

lemma norm_ξc (ξ : E3) : ‖ξc ξ‖ = ‖ξ‖ := by
  simp [EuclideanSpace.norm_eq, ξc, Complex.norm_real]

/-- Pointwise symbol identity: `(ℙ_ξ - 1) ∇·(c) = ∇ p̂` with `p̂ = -∑ ξᵢξⱼ/|ξ|² cᵢⱼ`. -/
lemma leray_sub_id_symbol (ξ : E3) (c : Fin 3 → Fin 3 → ℂ) (k : Fin 3) :
    (lerSym ξ (∑ i : Fin 3, ∑ j : Fin 3, sym j ξ • Nonlinear.embedCLM i (c i j)) -
        ∑ i : Fin 3, ∑ j : Fin 3, sym j ξ • Nonlinear.embedCLM i (c i j)) k =
      sym k ξ * (-∑ i : Fin 3, ∑ j : Fin 3,
        ((rieszCoeff i j ξ : ℂ) • Nonlinear.embedCLM 0 (c i j))) 0 := by
  rw [lerSym_apply, sub_sub_cancel_left, norm_ξc]
  have hinner : inner ℂ (ξc ξ) (∑ i : Fin 3, ∑ j : Fin 3, sym j ξ • Nonlinear.embedCLM i (c i j)) =
      ∑ i : Fin 3, ∑ j : Fin 3, sym j ξ * ((ξ i : ℝ) : ℂ) * c i j := by
    simp only [inner_sum, inner_smul_right]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Nonlinear.embedCLM_apply, EuclideanSpace.inner_single_right]
    simp only [ξc, PiLp.toLp_apply, starRingEnd_apply]
    rw [show star ((ξ i : ℝ) : ℂ) = ((ξ i : ℝ) : ℂ) from Complex.conj_ofReal _]
    ring
  rw [hinner]
  simp only [PiLp.neg_apply, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply,
    Nonlinear.embedCLM_apply, PiLp.single_apply, smul_eq_mul, if_true]
  by_cases h0 : ‖ξ‖ = 0
  · have hξ : ξ = 0 := norm_eq_zero.1 h0
    subst hξ
    simp [sym, ξc]
  · simp only [rieszCoeff, if_neg h0, ξc, sym]
    have hn : ((‖ξ‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 2 h0
    simp only [Fin.sum_univ_three]
    push_cast
    field_simp

lemma Lp_coeFn_sum {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {p : ℝ≥0∞}
    {μ : Measure α} {ι : Type*} (s : Finset ι) (f : ι → Lp E p μ) :
    (⇑(∑ i ∈ s, f i) : α → E) =ᵐ[μ] fun a => ∑ i ∈ s, (f i : α → E) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Lp.coeFn_zero E p μ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2, Finset.sum_insert ha]

/-- Scalar convolution `∫ Fᵢ(t) Gⱼ(ξ - t) dt`. -/
def cc (F G : E3 → V) (i j : Fin 3) (ξ : E3) : ℂ := ∫ t, F t i * G (ξ - t) j

/-- `embedCLM` as a linear isometry. -/
def embedLI (i : Fin 3) : ℂ →ₗᵢ[ℂ] V :=
  { toLinearMap := (Nonlinear.embedCLM i).toLinearMap
    norm_map' := Nonlinear.norm_embedCLM_apply i }

lemma conv_Lij (F G : E3 → V) (i j : Fin 3) (ξ : E3) :
    (F ⋆[Nonlinear.Lij i j] G) ξ = Nonlinear.embedCLM i (cc F G i j ξ) := by
  rw [convolution_def]
  exact (embedLI i).integral_comp_comm (fun t => F t i * G (ξ - t) j)

lemma conv_Lprod (F G : E3 → V) (i j : Fin 3) (ξ : E3) :
    (F ⋆[Lprod i j] G) ξ = Nonlinear.embedCLM 0 (cc F G i j ξ) := by
  rw [convolution_def]
  exact (embedLI 0).integral_comp_comm (fun t => F t i * G (ξ - t) j)

lemma coeFn_divTensor_vol {s : ℕ} (hs : 3 ≤ s) (U : Hm s) :
    (divTensor hs U : E3 → V) =ᵐ[volume] fun ξ => ∑ i : Fin 3, ∑ j : Fin 3,
      sym j ξ • Nonlinear.embedCLM i (cc (U : E3 → V) (U : E3 → V) i j ξ) := by
  have h1 := (ac_vol (s - 1)).ae_le (Lp_coeFn_sum Finset.univ (fun i : Fin 3 => ∑ j : Fin 3,
    dH (one_le_of_three hs) j (ProductHm.mulF (Nonlinear.Lij i j) hs U U)))
  have h2 : ∀ i : Fin 3, ∀ᵐ ξ ∂volume, (⇑(∑ j : Fin 3,
      dH (one_le_of_three hs) j (ProductHm.mulF (Nonlinear.Lij i j) hs U U)) : E3 → V) ξ =
      ∑ j : Fin 3, (dH (one_le_of_three hs) j
        (ProductHm.mulF (Nonlinear.Lij i j) hs U U) : E3 → V) ξ := fun i =>
    (ac_vol (s - 1)).ae_le (Lp_coeFn_sum Finset.univ _)
  have h3 : ∀ i j : Fin 3, ∀ᵐ ξ ∂volume, (dH (one_le_of_three hs) j
      (ProductHm.mulF (Nonlinear.Lij i j) hs U U) : E3 → V) ξ =
      sym j ξ • Nonlinear.embedCLM i (cc (U : E3 → V) (U : E3 → V) i j ξ) := by
    intro i j
    filter_upwards [(ac_vol (s - 1)).ae_le (coeFn_dH (one_le_of_three hs) j
      (ProductHm.mulF (Nonlinear.Lij i j) hs U U)),
      (ac_vol s).ae_le (ProductHm.coeFn_mulF (Nonlinear.Lij i j) hs U U)] with ξ ha hb
    rw [ha, Nonlinear.derivSym_apply, hb, conv_Lij]
  filter_upwards [h1, ae_all_iff.2 h2, ae_all_iff.2 fun i => ae_all_iff.2 (h3 i)]
    with ξ ha hb hc
  unfold divTensor
  rw [ha]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hb i]
  exact Finset.sum_congr rfl fun j _ => hc i j

lemma coeFn_lerayPressureHm_vol {s : ℕ} (hs : 3 ≤ s) (U : Hm s) :
    (lerayPressureHm hs U : E3 → V) =ᵐ[volume] fun ξ => -∑ i : Fin 3, ∑ j : Fin 3,
      (rieszCoeff i j ξ : ℂ) • Nonlinear.embedCLM 0 (cc (U : E3 → V) (U : E3 → V) i j ξ) := by
  have h0 := (ac_vol s).ae_le (Lp.coeFn_neg (∑ i : Fin 3, ∑ j : Fin 3,
    rieszMul i j s (ProductHm.mulF (Lprod i j) hs U U)))
  have h1 := (ac_vol s).ae_le (Lp_coeFn_sum Finset.univ (fun i : Fin 3 => ∑ j : Fin 3,
    rieszMul i j s (ProductHm.mulF (Lprod i j) hs U U)))
  have h2 : ∀ i : Fin 3, ∀ᵐ ξ ∂volume, (⇑(∑ j : Fin 3,
      rieszMul i j s (ProductHm.mulF (Lprod i j) hs U U)) : E3 → V) ξ =
      ∑ j : Fin 3, (rieszMul i j s (ProductHm.mulF (Lprod i j) hs U U) : E3 → V) ξ := fun i =>
    (ac_vol s).ae_le (Lp_coeFn_sum Finset.univ _)
  have h3 : ∀ i j : Fin 3, ∀ᵐ ξ ∂volume,
      (rieszMul i j s (ProductHm.mulF (Lprod i j) hs U U) : E3 → V) ξ =
      (rieszCoeff i j ξ : ℂ) • Nonlinear.embedCLM 0 (cc (U : E3 → V) (U : E3 → V) i j ξ) := by
    intro i j
    filter_upwards [(ac_vol s).ae_le (coeFn_wmul (rieszSym i j) (rieszSym_meas i j) 1
      zero_le_one (bound_riesz i j s) (ProductHm.mulF (Lprod i j) hs U U)),
      (ac_vol s).ae_le (ProductHm.coeFn_mulF (Lprod i j) hs U U)] with ξ ha hb
    rw [rieszMul, ha, rieszSym_apply, hb, conv_Lprod]
  filter_upwards [h0, h1, ae_all_iff.2 h2, ae_all_iff.2 fun i => ae_all_iff.2 (h3 i)]
    with ξ hn ha hb hc
  unfold lerayPressureHm
  rw [hn, Pi.neg_apply, ha]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hb i]
  exact Finset.sum_congr rfl fun j _ => hc i j

/-- **Fourier-side pressure identity.** Componentwise,
`(ℙ - 1) ∇·(U ⊗ U) = ∇ p̂` with `p̂ = lerayPressureHm U` (in slot `0`). -/
lemma leray_sub_divTensor_coord_ae {s : ℕ} (hs : 3 ≤ s) (U : Hm s) (k : Fin 3) :
    (fun ξ => ((lerayH (s - 1) (divTensor hs U) - divTensor hs U : Hm (s - 1)) : E3 → V) ξ k) =ᵐ[volume]
      fun ξ => (dH (one_le_of_three hs) k (lerayPressureHm hs U) : E3 → V) ξ 0 := by
  filter_upwards [(ac_vol (s - 1)).ae_le (Lp.coeFn_sub (lerayH (s - 1) (divTensor hs U))
      (divTensor hs U)),
    (ac_vol (s - 1)).ae_le (MildDivFree.coeFn_lerayH (s - 1) (divTensor hs U)),
    coeFn_divTensor_vol hs U,
    (ac_vol (s - 1)).ae_le (coeFn_dH (one_le_of_three hs) k (lerayPressureHm hs U)),
    coeFn_lerayPressureHm_vol hs U] with ξ h1 h2 h3 h4 h5
  rw [h1, Pi.sub_apply, h2, h3, h4, Nonlinear.derivSym_apply, h5, PiLp.smul_apply, smul_eq_mul]
  exact leray_sub_id_symbol ξ _ k

lemma fourierInv_congr_ae_scalar {f g : E3 → ℂ} (h : f =ᵐ[volume] g) (x : E3) :
    𝓕⁻ f x = 𝓕⁻ g x := by
  rw [fourierInv_eq_fourier_neg, fourierInv_eq_fourier_neg, Real.fourier_eq, Real.fourier_eq]
  exact integral_congr_ae (h.mono fun ξ hξ => by simp only [hξ])

lemma lerayPressure_eq {s : ℕ} (hs : 3 ≤ s) (U : Hm s) :
    lerayPressure hs U = fun y => (𝓕⁻ (lerayPressureHm hs U : E3 → V) y 0).re := by
  funext y
  rw [lerayPressure, physicalInv_def]
  rfl

lemma hasFDerivAt_lerayPressure {s : ℕ} (hs : 3 ≤ s) (U : Hm s) (x : E3) :
    HasFDerivAt (lerayPressure hs U)
      ((Complex.reCLM.comp (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℂ) 0)).comp
        (spatFDeriv hs (lerayPressureHm hs U) x)) x := by
  rw [lerayPressure_eq]
  exact (Complex.reCLM.comp (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℂ) 0)).hasFDerivAt.comp x
    (hasFDerivAt_fourierInv hs _ x)

open NavierStokes3D in
/-- **Pressure gradient.** The physical field of `(ℙ - 1) ∇·(U ⊗ U)` is the
gradient of the Leray pressure `lerayPressure U`. -/
theorem realify_fourierInv_leray_sub {s : ℕ} (hs : 3 ≤ s) (U : Hm s) (x : E3) :
    realify (𝓕⁻ ((lerayH (s - 1) (divTensor hs U) - divTensor hs U : Hm (s - 1)) : E3 → V) x) =
      pressureGradient (lerayPressure hs U) x := by
  ext k
  change (𝓕⁻ ((lerayH (s - 1) (divTensor hs U) - divTensor hs U : Hm (s - 1)) : E3 → V) x k).re = _
  rw [← MildDivFree.fourierInv_proj (integrable_of_Hm (two_le_pred_of_three hs) _) k x,
    fourierInv_congr_ae_scalar (leray_sub_divTensor_coord_ae hs U k) x,
    MildDivFree.fourierInv_proj (integrable_of_Hm (two_le_pred_of_three hs) _) 0 x]
  unfold pressureGradient
  rw [gradient_coord _ x k (hasFDerivAt_lerayPressure hs U x).differentiableAt,
    (hasFDerivAt_lerayPressure hs U x).fderiv]
  simp only [ContinuousLinearMap.comp_apply, spatFDeriv_single, PiLp.proj_apply,
    Complex.reCLM_apply]

/-! ## The nonlinearity in physical variables -/

open NavierStokes3D in
/-- **Physical nonlinearity.** For a real, Leray-fixed `U ∈ Ĥ^s` (`s ≥ 3`),
the physical field of `NSN U = ℙ ∇·(U ⊗ U)` is `(u·∇)u + ∇p` with the Leray
pressure `p = lerayPressure U`. -/
theorem realify_fourierInv_NSN {s : ℕ} (hs : 3 ≤ s) {U : Hm s}
    (hdiv : lerayH s U = U) (hreal : ∀ y : E3, ∀ k : Fin 3, (𝓕⁻ (U : E3 → V) y k).im = 0)
    (x : E3) :
    realify (𝓕⁻ (NSN hs U : E3 → V) x) =
      convective (physicalOfHm U) (physicalOfHm U) x +
        pressureGradient (lerayPressure hs U) x := by
  have hsplit : NSN hs U = divTensor hs U +
      (lerayH (s - 1) (divTensor hs U) - divTensor hs U) := by
    rw [NSN]; abel
  rw [hsplit, fourierInv_eq_evMap (two_le_pred_of_three hs), map_add, ← fourierInv_eq_evMap,
    ← fourierInv_eq_evMap, realify_add, realify_fourierInv_divTensor hs hdiv hreal,
    realify_fourierInv_leray_sub]

lemma coe_rec_Hm {a b : ℕ} (e : a = b) (G : Hm a) :
    (((e ▸ G : Hm b)) : E3 → V) = (G : E3 → V) := by
  cases e; rfl

lemma coe_NSNsucc {k : ℕ} (hk : 2 ≤ k) (U : Hm (k + 1)) :
    ((NSNsucc hk U : Hm k) : E3 → V) = (NSN (three_le_succ hk) U : E3 → V) :=
  coe_rec_Hm (Nat.add_sub_cancel k 1) _

open NavierStokes3D in
theorem physicalOfHm_NSNsucc {k : ℕ} (hk : 2 ≤ k) {U : Hm (k + 1)}
    (hdiv : lerayH (k + 1) U = U)
    (hreal : ∀ y : E3, ∀ i : Fin 3, (𝓕⁻ (U : E3 → V) y i).im = 0) (x : E3) :
    physicalOfHm (NSNsucc hk U) x =
      convective (physicalOfHm U) (physicalOfHm U) x +
        pressureGradient (lerayPressure (three_le_succ hk) U) x := by
  unfold physicalOfHm
  rw [coe_NSNsucc]
  exact realify_fourierInv_NSN (three_le_succ hk) hdiv hreal x

/-! ## The Laplacian in physical variables -/

lemma fourierInv_finset_sum_V {h : Fin 3 → E3 → V} (hh : ∀ i, Integrable (h i)) (x : E3) :
    (∑ i : Fin 3, 𝓕⁻ (h i) x) = 𝓕⁻ (fun ξ => ∑ i : Fin 3, h i ξ) x := by
  simp only [fourierInv_eq_fourier_neg, Real.fourier_eq, Finset.smul_sum]
  rw [integral_finset_sum _ fun i _ => (Real.fourierIntegral_convergent_iff (-x)).mpr (hh i)]

lemma fderiv_physicalOfHm_single {m : ℕ} (hm : 3 ≤ m) (G : Hm m) (j : Fin 3) :
    (fun y => fderiv ℝ (physicalOfHm G) y (EuclideanSpace.single j 1)) =
      physicalOfHm (dH (one_le_of_three hm) j G) := by
  funext y
  have hd : HasFDerivAt (physicalOfHm G) (realifyCLM.comp (spatFDeriv hm G y)) y := by
    rw [physicalOfHm_eq_comp]
    exact realifyCLM.hasFDerivAt.comp y (hasFDerivAt_fourierInv hm G y)
  rw [hd.fderiv, ContinuousLinearMap.comp_apply, spatFDeriv_single, realifyCLM_apply]
  rfl

open NavierStokes3D HeatDeriv in
/-- **Laplacian.** For `G ∈ Ĥ^{m+2}` (`m ≥ 2`), the physical Laplacian of
`physicalOfHm G` is the physical field of `lapH m G`. -/
theorem laplacian_physicalOfHm {m : ℕ} (hm : 2 ≤ m) (G : Hm (m + 2)) (x : E3) :
    laplacian (physicalOfHm G) x = physicalOfHm (lapH m G) x := by
  have hm3 : 3 ≤ m + 2 := by omega
  have hm3' : 3 ≤ m + 2 - 1 := by omega
  unfold laplacian
  simp only [fderiv_physicalOfHm_single hm3]
  have hterm : ∀ i : Fin 3,
      fderiv ℝ (physicalOfHm (dH (one_le_of_three hm3) i G)) x (EuclideanSpace.single i 1) =
        realifyCLM (𝓕⁻ (dH (one_le_of_three hm3') i (dH (one_le_of_three hm3) i G) : E3 → V) x) :=
    fun i => congrFun (fderiv_physicalOfHm_single hm3' _ i) x
  simp only [hterm]
  rw [← map_sum realifyCLM, fourierInv_finset_sum_V
    (fun i => integrable_of_Hm (two_le_pred_of_three hm3') _)]
  unfold physicalOfHm
  rw [← realifyCLM_apply]
  congr 1
  refine fourierInv_congr_ae ?_ x
  have hd : ∀ i : Fin 3, ∀ᵐ ξ ∂volume,
      (dH (one_le_of_three hm3') i (dH (one_le_of_three hm3) i G) : E3 → V) ξ =
        sym i ξ • sym i ξ • (G : E3 → V) ξ := by
    intro i
    filter_upwards [(ac_vol (m + 2 - 1 - 1)).ae_le (coeFn_dH (one_le_of_three hm3') i
        (dH (one_le_of_three hm3) i G)),
      (ac_vol (m + 2 - 1)).ae_le (coeFn_dH (one_le_of_three hm3) i G)] with ξ h1 h2
    rw [h1, Nonlinear.derivSym_apply, h2, Nonlinear.derivSym_apply]
  filter_upwards [ae_all_iff.2 hd, (ac_vol m).ae_le (coeFn_lapH m G)] with ξ h1 h2
  rw [h2]
  simp only [h1, smul_smul, ← Finset.sum_smul]
  congr 1
  have hn : ‖ξ‖ ^ 2 = ∑ i : Fin 3, ξ i ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    simp
  rw [hn]
  simp only [sym, Fin.sum_univ_three]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ## Item 3(D): the pointwise momentum equation along the mild path -/

open MildTimeDeriv MildPathSmooth RepairedTether NavierStokes3D HeatDeriv

/-- Leray pressure of the realized mild path (from its `Ĥ³` slice). -/
def presMild {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀) (hdec : FeffermanDecay u₀)
    {ν : ℝ} (hν : 0 < ν) : TimeDependentPressure :=
  fun t => lerayPressure (le_refl 3)
    (ContinuousMap.IccExtend (Tfeff_nonneg hf hdec hν)
      (persistPath hf hdec hν (by norm_num : 2 ≤ 2)) t)

lemma incl_self_Hm {m : ℕ} (h : m ≤ m) (G : Hm m) : incl h G = G :=
  Lp.ext (ProductHm.coeFn_incl h G)

lemma IccExtend_persistPath_apply {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀)
    (hdec : FeffermanDecay u₀) {ν : ℝ} (hν : 0 < ν) {k : ℕ} (hk : 2 ≤ k) (s : ℝ) :
    ContinuousMap.IccExtend (Tfeff_nonneg hf hdec hν) (persistPath hf hdec hν hk) s =
      persistPath hf hdec hν hk (projIcc 0 (Tfeff hf hdec hν) (Tfeff_nonneg hf hdec hν) s) := by
  rw [ContinuousMap.coe_IccExtend]; rfl

/-- The realized mild field is the physical field of any included persisted path. -/
lemma physicalMild_eq_inclExt {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀)
    (hdec : FeffermanDecay u₀) {ν : ℝ} (hν : 0 < ν) {k : ℕ} (hk : 2 ≤ k) {m : ℕ}
    (hle : m ≤ k + 1) (s : ℝ) :
    physicalMild hf hdec hν s =
      physicalOfHm (inclExt hle (Tfeff_nonneg hf hdec hν) (persistPath hf hdec hν hk) s) := by
  unfold physicalMild inclExt
  rw [physicalOfHm_incl, IccExtend_persistPath_apply, IccExtend_persistPath_apply]
  exact physicalOfHm_persistPath_eq hf hdec hν _ hk _

/-- The `Ĥ³` slice of any persisted path is the `k = 2` slice. -/
lemma inclExt_three_eq {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀)
    (hdec : FeffermanDecay u₀) {ν : ℝ} (hν : 0 < ν) {k : ℕ} (hk : 2 ≤ k)
    (hle : 3 ≤ k + 1) (s : ℝ) :
    inclExt hle (Tfeff_nonneg hf hdec hν) (persistPath hf hdec hν hk) s =
      ContinuousMap.IccExtend (Tfeff_nonneg hf hdec hν)
        (persistPath hf hdec hν (by norm_num : 2 ≤ 2)) s := by
  unfold inclExt
  rw [IccExtend_persistPath_apply, IccExtend_persistPath_apply]
  have h := congrArg (fun u : MildExistence.XT (Tfeff hf hdec hν) =>
      u (projIcc 0 (Tfeff hf hdec hν) (Tfeff_nonneg hf hdec hν) s))
    (inclMap_persistPath_unique hf hdec hν hk (by norm_num : 2 ≤ 2))
  change incl (three_le_succ hk) _ = incl (three_le_succ (by norm_num : 2 ≤ 2)) _ at h
  rw [incl_irrel hle (three_le_succ hk), h, incl_self_Hm]

/-- Every `Ĥ³` slice of the mild path is Leray-fixed (given divergence-free data). -/
lemma lerayH_IccExtend {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀)
    (hdec : FeffermanDecay u₀) (hdiv : ∀ x, div u₀ x = 0) {ν : ℝ} (hν : 0 < ν) (s : ℝ) :
    lerayH 3 (ContinuousMap.IccExtend (Tfeff_nonneg hf hdec hν)
      (persistPath hf hdec hν (by norm_num : 2 ≤ 2)) s) =
      ContinuousMap.IccExtend (Tfeff_nonneg hf hdec hν)
        (persistPath hf hdec hν (by norm_num : 2 ≤ 2)) s := by
  rw [IccExtend_persistPath_apply]
  exact MildDivFree.lerayH_mildS (by norm_num : 2 ≤ 2) (Tfeff_nonneg hf hdec hν) hν
    (MildDivFree.lerayH_toHmFeff hf hdec hdiv 3)
    (persistPath_mildS hf hdec hν (by norm_num : 2 ≤ 2)) _

/-- Every `Ĥ³` slice of the mild path has a real inverse Fourier transform. -/
lemma fourierInv_IccExtend_im {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀)
    (hdec : FeffermanDecay u₀) {ν : ℝ} (hν : 0 < ν) (s : ℝ) (y : E3) (i : Fin 3) :
    (𝓕⁻ ((ContinuousMap.IccExtend (Tfeff_nonneg hf hdec hν)
      (persistPath hf hdec hν (by norm_num : 2 ≤ 2)) s : Hm 3) : E3 → V) y i).im = 0 := by
  rw [IccExtend_persistPath_apply]
  exact MildReal.fourierInv_im_eq_zero
    (MildReal.refl_persistPath_high hf hdec hν (by norm_num : 2 ≤ 2) _) y i

/-- **Item 3(D): the momentum equation.** For divergence-free Fefferman data,
the realized mild field `physicalMild` and its Leray pressure `presMild`
satisfy the pointwise Navier–Stokes momentum equation on `[0, Tfeff) × ℝ³`,
with the one-sided time derivative of `IsFeffermanSolutionOn`. -/
theorem momentum_physicalMild {u₀ : VelocityField} (hf : ContDiff ℝ ∞ u₀)
    (hdec : FeffermanDecay u₀) (hdiv : ∀ x, div u₀ x = 0) {ν : ℝ} (hν : 0 < ν)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) (Tfeff hf hdec hν)) (x : E3) :
    derivWithin (fun s => physicalMild hf hdec hν s x) (Ici 0) t +
        convective (physicalMild hf hdec hν t) (physicalMild hf hdec hν t) x +
        pressureGradient (presMild hf hdec hν t) x =
      ν • laplacian (physicalMild hf hdec hν t) x + 0 := by
  have hT := Tfeff_nonneg hf hdec hν
  have hk4 : 2 ≤ 4 := by norm_num
  have hm2 : 2 + 2 ≤ 4 := le_refl 4
  set u := persistPath hf hdec hν hk4 with hu_def
  have hu := persistPath_mildS hf hdec hν hk4
  set γ := inclExt (le_succ_of_add_two_le hm2) hT u with hγ_def
  set L : Hm 2 →L[ℝ] E3 := realifyCLM.comp (evMap (le_refl 2) x) with hL
  have hfun : (fun s => physicalMild hf hdec hν s x) = fun s => L (γ s) := by
    funext s
    rw [physicalMild_eq_inclExt hf hdec hν hk4 (le_succ_of_add_two_le hm2) s]
    rfl
  have hγd := hasDerivWithinAt_mildS_incl_Ico hk4 hm2 hν hT hu ht
  have hmem : Ico 0 (Tfeff hf hdec hν) ∈ 𝓝[Ici 0] t := by
    rw [← Ici_inter_Iio]
    exact inter_mem_nhdsWithin _ (Iio_mem_nhds ht.2)
  have hder : HasDerivWithinAt (fun s => physicalMild hf hdec hν s x)
      (L (mildSDeriv hk4 hm2 hν hT (FeffermanSobolev.toHmFeff u₀ hf hdec (4 + 1)) u t))
      (Ici 0) t := by
    rw [hfun]
    exact (L.hasFDerivAt.comp_hasDerivWithinAt t hγd).mono_of_mem_nhdsWithin hmem
  rw [hder.derivWithin (uniqueDiffOn_Ici 0 t ht.1),
    mildSDeriv_eq_NSNsucc hk4 (le_refl 2) hm2 hν hT hu ⟨ht.1, le_of_lt ht.2⟩,
    map_sub, map_smul]
  have hlap : L (lapH 2 (inclExt (add_two_le_succ hm2) hT u t)) =
      laplacian (physicalMild hf hdec hν t) x := by
    rw [physicalMild_eq_inclExt hf hdec hν hk4 (add_two_le_succ hm2) t,
      laplacian_physicalOfHm (le_refl 2)]
    rfl
  have h3 := inclExt_three_eq hf hdec hν hk4 (le_succ_succ (InclNSN.le_of_add_two_le hm2)) t
  have hnsn : L (NSNsucc (le_refl 2)
      (inclExt (le_succ_succ (InclNSN.le_of_add_two_le hm2)) hT u t)) =
      convective (physicalMild hf hdec hν t) (physicalMild hf hdec hν t) x +
        pressureGradient (presMild hf hdec hν t) x := by
    change physicalOfHm _ x = _
    rw [h3, physicalOfHm_NSNsucc (le_refl 2) (lerayH_IccExtend hf hdec hdiv hν t)
      (fourierInv_IccExtend_im hf hdec hν t) x]
    rfl
  rw [hlap, hnsn]
  abel

#print axioms MildMomentum.fourier_conv_eq
#print axioms MildMomentum.fourierInv_mulF
#print axioms MildMomentum.fourierInv_dH_mulF_Lij
#print axioms MildMomentum.sum_fourierInv_dH_self
#print axioms MildMomentum.realify_fourierInv_divTensor
#print axioms MildMomentum.leray_sub_divTensor_coord_ae
#print axioms MildMomentum.realify_fourierInv_leray_sub
#print axioms MildMomentum.realify_fourierInv_NSN
#print axioms MildMomentum.physicalOfHm_NSNsucc
#print axioms MildMomentum.laplacian_physicalOfHm
#print axioms MildMomentum.momentum_physicalMild

end MildMomentum
