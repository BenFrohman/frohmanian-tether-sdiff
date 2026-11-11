import Scratch.LerayHeat
import Scratch.R3BKMContinuation
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! # Fourier-side Sobolev energy on `L²(ℝ³; ℂ³)` matched to `R3BKM.sobolevEnergy`

Key analytic input: for `g : ℝ³ → ℂ³` of class `C¹` with `g, ∂_m g ∈ L²`,
`𝓕(∂_m g) = 2πi ⟪ξ, m⟫ 𝓕 g` a.e. (via tempered distributions and integration by parts). -/

open MeasureTheory SchwartzMap FourierTransform Real LineDeriv
open scoped ENNReal ContDiff InnerProductSpace

noncomputable section
namespace SobolevFourier

open LerayHeat

instance : ENNReal.HolderTriple 2 2 1 := ⟨by rw [inv_one]; exact ENNReal.inv_two_add_inv_two⟩

set_option backward.isDefEq.respectTransparency false in
/-- Integration by parts against a Schwartz test function gives the distributional derivative. -/
theorem toTD_deriv {g : E3 → V} (hg : ContDiff ℝ 1 g) (m : E3) (h2 : MemLp g 2)
    (h2' : MemLp (fun x => fderiv ℝ g x m) 2) :
    ∂_{m} ((h2.toLp g : L2V) : 𝓢'(E3, V)) = ((h2'.toLp _ : L2V) : 𝓢'(E3, V)) := by
  ext1 ψ
  rw [TemperedDistribution.lineDerivOp_apply_apply]
  simp only [Lp.toTemperedDistribution_apply]
  have hψ2 : ∀ φ : 𝓢(E3, ℂ), MemLp (φ : E3 → ℂ) 2 := fun φ => φ.memLp 2
  have e1 : ∫ x, (-∂_{m} ψ) x • ((h2.toLp g : L2V) : E3 → V) x = ∫ x, (-∂_{m} ψ) x • g x :=
    integral_congr_ae (by filter_upwards [h2.coeFn_toLp] with x hx; rw [hx])
  have e2 : ∫ x, ψ x • ((h2'.toLp _ : L2V) : E3 → V) x = ∫ x, ψ x • fderiv ℝ g x m :=
    integral_congr_ae (by filter_upwards [h2'.coeFn_toLp] with x hx; rw [hx])
  rw [e1, e2]
  have hibp := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := volume)
    (f := (ψ : E3 → ℂ)) (g := g) (v := m)
    ((h2.smul (hψ2 (∂_{m} ψ)) (r := 1)) |> memLp_one_iff_integrable.1)
    ((h2'.smul (hψ2 ψ) (r := 1)) |> memLp_one_iff_integrable.1)
    ((h2.smul (hψ2 ψ) (r := 1)) |> memLp_one_iff_integrable.1)
    (fun x _ => ψ.differentiableAt) (fun x _ => hg.differentiable one_ne_zero x)
  rw [hibp]
  simp only [SchwartzMap.neg_apply, neg_smul, integral_neg, lineDerivOp_apply_eq_fderiv]

set_option backward.isDefEq.respectTransparency false in
/-- **Fourier transform of a derivative** (`L²` version): `𝓕(∂_m g) = 2πi⟪ξ,m⟫ 𝓕g` a.e. -/
theorem fourier_deriv {g : E3 → V} (hg : ContDiff ℝ 1 g) (m : E3) (h2 : MemLp g 2)
    (h2' : MemLp (fun x => fderiv ℝ g x m) 2) :
    ((𝓕 (h2'.toLp _ : L2V) : L2V) : E3 → V) =ᵐ[volume]
      fun ξ => ((2 * π * Complex.I) * ((inner ℝ ξ m : ℝ) : ℂ)) • ((𝓕 (h2.toLp g : L2V) : L2V) : E3 → V) ξ := by
  set G : L2V := h2.toLp g
  set G' : L2V := h2'.toLp _
  have hT : ((𝓕 G' : L2V) : 𝓢'(E3, V)) = (2 * π * Complex.I) •
      TemperedDistribution.smulLeftCLM V (fun ξ => ((inner ℝ ξ m : ℝ) : ℂ)) ((𝓕 G : L2V) : 𝓢'(E3, V)) := by
    rw [← Lp.fourier_toTemperedDistribution_eq, ← Lp.fourier_toTemperedDistribution_eq,
      show ((G' : L2V) : 𝓢'(E3, V)) = ∂_{m} ((G : L2V) : 𝓢'(E3, V)) from (toTD_deriv hg m h2 h2').symm,
      TemperedDistribution.fourier_lineDerivOp_eq]
  have htg : (fun ξ : E3 => ((inner ℝ ξ m : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  have hc : Continuous fun ξ : E3 => ((2 * π * Complex.I) * ((inner ℝ ξ m : ℝ) : ℂ)) := by fun_prop
  refine ae_eq_of_integral_contDiff_smul_eq ((Lp.memLp _).locallyIntegrable (by norm_num)) ?_ ?_
  · have := (((Lp.memLp (𝓕 G)).locallyIntegrable (by norm_num)).locallyIntegrableOn Set.univ
      ).continuousOn_smul isClosed_univ.isLocallyClosed hc.continuousOn
    exact locallyIntegrableOn_univ.1 this
  intro φ hφ hφc
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hφc.comp_left rfl
  have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ) := by fun_prop
  set ψ : 𝓢(E3, ℂ) := hg₁.toSchwartzMap hg₂
  have h1 := congrArg (fun T : 𝓢'(E3, V) => T ψ) hT
  change _ = (2 * π * Complex.I) • ((TemperedDistribution.smulLeftCLM V
    (fun ξ => ((inner ℝ ξ m : ℝ) : ℂ)) ((𝓕 G : L2V) : 𝓢'(E3, V))) ψ) at h1
  rw [TemperedDistribution.smulLeftCLM_apply_apply] at h1
  simp only [Lp.toTemperedDistribution_apply, SchwartzMap.smulLeftCLM_apply_apply htg] at h1
  have eψ : ∀ x, ψ x = (φ x : ℂ) := fun x => rfl
  simp only [eψ] at h1
  have r1 : ∀ x, φ x • ((𝓕 G' : L2V) : E3 → V) x = (φ x : ℂ) • ((𝓕 G' : L2V) : E3 → V) x :=
    fun x => (Complex.coe_smul _ _).symm
  simp only [r1]
  rw [h1, ← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_smul, ← Complex.coe_smul, smul_eq_mul]
  congr 1; ring

/-! ## Multi-index (word) derivatives -/

/-- Unit-vector tuple of a word `α`. -/
abbrev U {k : ℕ} (α : Fin k → Fin 3) : Fin k → E3 := fun j => EuclideanSpace.single (α j) (1 : ℝ)

/-- `∂_{α 0} ⋯ ∂_{α (k-1)} g`. -/
def dw {k : ℕ} (α : Fin k → Fin 3) (g : E3 → V) : E3 → V := fun x => iteratedFDeriv ℝ k g x (U α)

lemma contDiff_dw {g : E3 → V} (hg : ContDiff ℝ ∞ g) {k : ℕ} (α : Fin k → Fin 3) :
    ContDiff ℝ ∞ (dw α g) := by
  have h : ContDiff ℝ ∞ (iteratedFDeriv ℝ k g) := hg.iteratedFDeriv_right (by
    rw [show ((k : WithTop ℕ∞)) = ((k : ℕ∞) : WithTop ℕ∞) from rfl, ← WithTop.coe_add, top_add])
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E3) V (U α)).contDiff.comp h

lemma dw_zero (α : Fin 0 → Fin 3) (g : E3 → V) : dw α g = g := by
  funext x; simp [dw]

lemma dw_succ {g : E3 → V} (hg : ContDiff ℝ ∞ g) {k : ℕ} (α : Fin (k + 1) → Fin 3) :
    dw α g = fun x => fderiv ℝ (dw (Fin.tail α) g) x (EuclideanSpace.single (α 0) (1 : ℝ)) := by
  funext x
  simp only [dw]
  rw [iteratedFDeriv_succ_apply_left]
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k g) x :=
    (hg.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)) x
  show _ = fderiv ℝ (fun y => iteratedFDeriv ℝ k g y (U (Fin.tail α))) x _
  rw [fderiv_continuousMultilinear_apply_const_apply hd]
  rfl

/-- Fourier symbol of `∂_i`. -/
def sym (i : Fin 3) (ξ : E3) : ℂ := (2 * π * Complex.I) * ((ξ i : ℝ) : ℂ)

lemma inner_single (ξ : E3) (i : Fin 3) : inner ℝ ξ (EuclideanSpace.single i (1 : ℝ)) = ξ i := by
  simp [PiLp.inner_apply, apply_ite (inner ℝ _), Finset.sum_ite_eq', real_inner_eq_re_inner]

/-- **Fourier transform of a word derivative**: `𝓕(∂^α g) = (∏ⱼ 2πi ξ_{αⱼ}) 𝓕g`, provided all
right-factors `∂^{α_{j..}} g` lie in `L²` (here: all words of length `≤ k`). -/
theorem fourier_dw {g : E3 → V} (hg : ContDiff ℝ ∞ g) :
    ∀ (k : ℕ) (hL : ∀ j ≤ k, ∀ β : Fin j → Fin 3, MemLp (dw β g) 2) (α : Fin k → Fin 3),
    ((𝓕 ((hL k le_rfl α).toLp _ : L2V) : L2V) : E3 → V) =ᵐ[volume]
      fun ξ => (∏ j, sym (α j) ξ) • ((𝓕 ((hL 0 (Nat.zero_le _) Fin.elim0).toLp _ : L2V) : L2V) : E3 → V) ξ
  | 0, hL, α => by
    have : α = Fin.elim0 := Subsingleton.elim _ _
    subst this
    exact Filter.Eventually.of_forall fun ξ => by simp
  | k + 1, hL, α => by
    have hL' : ∀ j ≤ k, ∀ β : Fin j → Fin 3, MemLp (dw β g) 2 := fun j hj β => hL j (by omega) β
    have ih := fourier_dw hg k hL' (Fin.tail α)
    have hmem : MemLp (fun x => fderiv ℝ (dw (Fin.tail α) g) x
        (EuclideanSpace.single (α 0) (1 : ℝ))) 2 := by
      rw [← dw_succ hg]; exact hL (k + 1) le_rfl α
    have hfd := fourier_deriv ((contDiff_dw hg (Fin.tail α)).of_le (by simp))
      (EuclideanSpace.single (α 0) (1 : ℝ)) (hL k (Nat.le_succ k) (Fin.tail α)) hmem
    have e : (hL (k + 1) le_rfl α).toLp _ = (hmem.toLp _ : L2V) :=
      MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => by rw [dw_succ hg])
    rw [e]
    filter_upwards [hfd, ih] with ξ h1 h2
    rw [h1, h2, smul_smul, inner_single, Fin.prod_univ_succ]
    rfl

/-! ## Plancherel in `lintegral` form -/

lemma lintegral_sq_eq (G : L2V) : ∫⁻ x, ‖(G : E3 → V) x‖ₑ ^ 2 = eLpNorm G 2 volume ^ 2 := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

lemma eLpNorm_fourier (F : L2V) : eLpNorm (𝓕 F : L2V) 2 volume = eLpNorm F 2 volume := by
  have h := Lp.norm_fourier_eq F
  rw [Lp.norm_def, Lp.norm_def] at h
  exact (ENNReal.toReal_eq_toReal_iff' (Lp.eLpNorm_ne_top _) (Lp.eLpNorm_ne_top _)).1 h

/-- **Plancherel**: `∫ |𝓕F|² = ∫ |F|²`. -/
theorem lintegral_sq_fourier (F : L2V) :
    ∫⁻ ξ, ‖((𝓕 F : L2V) : E3 → V) ξ‖ₑ ^ 2 = ∫⁻ x, ‖(F : E3 → V) x‖ₑ ^ 2 := by
  rw [lintegral_sq_eq, lintegral_sq_eq, eLpNorm_fourier]

lemma memLp_two_of_lintegral {h : E3 → V} (hc : AEStronglyMeasurable h)
    (hfin : ∫⁻ x, ‖h x‖ₑ ^ 2 < ⊤) : MemLp h 2 := by
  refine ⟨hc, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
  have : ∀ x, ‖h x‖ₑ ^ (2 : ENNReal).toReal = ‖h x‖ₑ ^ 2 := fun x => by
    rw [show (2 : ENNReal).toReal = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  simp only [this]
  exact hfin.ne

/-! ## Complexification `ℝ³ → ℂ³` -/

lemma cplx_smul (c : ℝ) (a : E3) :
    WithLp.toLp 2 (fun i => (((c • a) i : ℝ) : ℂ)) = c • (WithLp.toLp 2 (fun i => ((a i : ℝ) : ℂ)) : V) := by
  ext i
  simp only [PiLp.smul_apply, WithLp.ofLp_toLp, smul_eq_mul, Complex.ofReal_mul]
  exact (Complex.real_smul).symm

/-- Coordinatewise complexification (a real-linear isometry). -/
def cplx : E3 →L[ℝ] V := LinearMap.toContinuousLinearMap
  { toFun := fun y => WithLp.toLp 2 (fun i => ((y i : ℝ) : ℂ))
    map_add' := fun a b => by ext i; simp
    map_smul' := cplx_smul }

lemma cplx_apply (y : E3) (i : Fin 3) : (cplx y) i = ((y i : ℝ) : ℂ) := rfl

lemma norm_cplx (y : E3) : ‖cplx y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp [cplx_apply, Complex.norm_real]

lemma enorm_cplx (y : E3) : ‖cplx y‖ₑ = ‖y‖ₑ := by
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, norm_cplx]

lemma dw_cplx {f : E3 → E3} (hf : ContDiff ℝ ∞ f) {k : ℕ} (α : Fin k → Fin 3) (x : E3) :
    dw α (cplx ∘ f) x = cplx (iteratedFDeriv ℝ k f x (U α)) := by
  simp only [dw]
  rw [cplx.iteratedFDeriv_comp_left hf.contDiffAt (by exact_mod_cast le_top)]
  rfl

/-! ## The Fourier-side `H^m` energy -/

/-- Fourier weight `∑_{k ≤ m} (∑ᵢ |2π ξᵢ|²)^k = ∑_{k ≤ m} (4π²|ξ|²)^k`. -/
def sobW (m : ℕ) (ξ : E3) : ℝ≥0∞ := ∑ k ∈ Finset.range (m + 1), (∑ i : Fin 3, ‖sym i ξ‖ₑ ^ 2) ^ k

/-- Fourier-side `H^m` energy of `F ∈ L²(ℝ³; ℂ³)`: `∫ sobW m ξ |𝓕F(ξ)|² dξ`. -/
def fourierEnergy (m : ℕ) (F : L2V) : ℝ≥0∞ := ∫⁻ ξ, sobW m ξ * ‖((𝓕 F : L2V) : E3 → V) ξ‖ₑ ^ 2

lemma sum_word_prod (k : ℕ) (a : Fin 3 → ℝ≥0∞) :
    ∑ α : Fin k → Fin 3, ∏ j, a (α j) = (∑ i, a i) ^ k := by
  have := Finset.prod_univ_sum (fun _ : Fin k => (Finset.univ : Finset (Fin 3))) (fun _ i => a i)
  rw [Fintype.piFinset_univ] at this
  rw [← this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma measurable_coe (F : L2V) : Measurable fun ξ => ‖(F : E3 → V) ξ‖ₑ ^ 2 :=
  (Lp.stronglyMeasurable F).measurable.enorm.pow_const _

lemma measurable_sym (i : Fin 3) : Measurable (sym i) := by unfold sym; fun_prop

set_option maxHeartbeats 800000 in
/-- **Exact match** `R3BKM.sobolevEnergy m f = fourierEnergy m (f as an L² field)` for every smooth
`f : ℝ³ → ℝ³` with finite `H^m` energy. -/
theorem sobolevEnergy_eq_fourierEnergy {f : E3 → E3} (hf : ContDiff ℝ ∞ f) (m : ℕ)
    (hE : R3BKM.sobolevEnergy m f < ⊤) :
    ∃ h0 : MemLp (cplx ∘ f) 2, R3BKM.sobolevEnergy m f = fourierEnergy m (h0.toLp _) := by
  set g := cplx ∘ f
  have hg : ContDiff ℝ ∞ g := cplx.contDiff.comp hf
  have hterm : ∀ k ∈ Finset.range (m + 1), ∀ α : Fin k → Fin 3,
      ∫⁻ x, ‖iteratedFDeriv ℝ k f x (fun j => EuclideanSpace.single (α j) (1 : ℝ))‖ₑ ^ 2 < ⊤ :=
    fun k hk α => (ENNReal.sum_lt_top.1 ((ENNReal.sum_lt_top.1 hE) k hk)) α (Finset.mem_univ _)
  have heq : ∀ k (α : Fin k → Fin 3), ∫⁻ x, ‖dw α g x‖ₑ ^ 2 =
      ∫⁻ x, ‖iteratedFDeriv ℝ k f x (fun j => EuclideanSpace.single (α j) (1 : ℝ))‖ₑ ^ 2 :=
    fun k α => lintegral_congr fun x => by rw [dw_cplx hf, enorm_cplx]
  have hL : ∀ j ≤ m, ∀ β : Fin j → Fin 3, MemLp (dw β g) 2 := fun j hj β =>
    memLp_two_of_lintegral (contDiff_dw hg β).continuous.aestronglyMeasurable
      (by rw [heq]; exact hterm j (Finset.mem_range.2 (by omega)) β)
  have h0 : MemLp g 2 := by simpa [dw_zero] using hL 0 (Nat.zero_le _) Fin.elim0
  refine ⟨h0, ?_⟩
  have e0 : (hL 0 (Nat.zero_le _) Fin.elim0).toLp _ = (h0.toLp g : L2V) :=
    MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => by rw [dw_zero])
  set Fh := ((𝓕 (h0.toLp g : L2V) : L2V) : E3 → V)
  unfold fourierEnergy sobW R3BKM.sobolevEnergy
  simp_rw [Finset.sum_mul]
  rw [lintegral_finset_sum _ (fun k _ => (Finset.measurable_sum _ fun i _ =>
    ((measurable_sym i).enorm.pow_const 2)).pow_const k |>.mul (measurable_coe _))]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  simp_rw [← sum_word_prod, Finset.sum_mul]
  rw [lintegral_finset_sum _ (fun α _ => (Finset.measurable_prod _ fun j _ =>
    ((measurable_sym (α j)).enorm.pow_const 2)).mul (measurable_coe _))]
  refine Finset.sum_congr rfl fun α _ => ?_
  have hLk : ∀ j ≤ k, ∀ β : Fin j → Fin 3, MemLp (dw β g) 2 := fun j hj β => hL j (hj.trans hk') β
  have hF := fourier_dw hg k hLk α
  have e0' : (hLk 0 (Nat.zero_le _) Fin.elim0).toLp _ = (h0.toLp g : L2V) :=
    MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => by rw [dw_zero])
  rw [e0'] at hF
  have h1 : ∫⁻ x, ‖dw α g x‖ₑ ^ 2 = ∫⁻ x, ‖(((hLk k le_rfl α).toLp _ : L2V) : E3 → V) x‖ₑ ^ 2 :=
    lintegral_congr_ae (by filter_upwards [(hLk k le_rfl α).coeFn_toLp] with x hx; rw [hx])
  rw [← heq, h1, ← lintegral_sq_fourier]
  refine lintegral_congr_ae ?_
  filter_upwards [hF] with ξ hξ
  rw [hξ, enorm_smul, mul_pow]
  congr 1
  rw [Finset.prod_pow]
  congr 1
  simp only [enorm_eq_nnnorm, nnnorm_prod, ENNReal.coe_finset_prod]

lemma enorm_sym_sq (i : Fin 3) (ξ : E3) : ‖sym i ξ‖ₑ ^ 2 = ENNReal.ofReal (4 * π ^ 2 * (ξ i) ^ 2) := by
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  congr 1
  simp only [sym, norm_mul, Complex.norm_real, Complex.norm_I, Complex.norm_ofNat, Real.norm_eq_abs,
    abs_of_pos pi_pos, mul_one]
  rw [mul_pow, sq_abs]; ring

lemma sum_sym_sq (ξ : E3) : ∑ i, ‖sym i ξ‖ₑ ^ 2 = ENNReal.ofReal (4 * π ^ 2 * ‖ξ‖ ^ 2) := by
  simp_rw [enorm_sym_sq]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity), EuclideanSpace.norm_sq_eq,
    Finset.mul_sum]
  simp [Real.norm_eq_abs, sq_abs]

/-- The weight is `∑_{k ≤ m} (4π²|ξ|²)^k`. -/
theorem sobW_eq (m : ℕ) (ξ : E3) :
    sobW m ξ = ENNReal.ofReal (∑ k ∈ Finset.range (m + 1), (4 * π ^ 2 * ‖ξ‖ ^ 2) ^ k) := by
  rw [sobW, sum_sym_sq, ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ENNReal.ofReal_pow (by positivity)]

/-- `hsSq 3 f` (R3BKMContinuation.lean:37) equals the Fourier-side `H³` energy. -/
theorem hsSq_eq_fourierEnergy {f : E3 → E3} (hf : ContDiff ℝ ∞ f)
    (hE : R3BKM.sobolevEnergy 3 f < ⊤) :
    ∃ h0 : MemLp (cplx ∘ f) 2, R3BKM.hsSq 3 f = (fourierEnergy 3 (h0.toLp _)).toReal ∧
      fourierEnergy 3 (h0.toLp _) < ⊤ := by
  obtain ⟨h0, he⟩ := sobolevEnergy_eq_fourierEnergy hf 3 hE
  exact ⟨h0, by rw [R3BKM.hsSq, he], he ▸ hE⟩

end SobolevFourier

#print axioms SobolevFourier.toTD_deriv
#print axioms SobolevFourier.fourier_deriv
#print axioms SobolevFourier.fourier_dw
#print axioms SobolevFourier.lintegral_sq_fourier
#print axioms SobolevFourier.sobolevEnergy_eq_fourierEnergy
#print axioms SobolevFourier.sobW_eq
#print axioms SobolevFourier.hsSq_eq_fourierEnergy
