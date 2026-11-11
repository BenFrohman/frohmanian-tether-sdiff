import Scratch.ProductHm
import Scratch.Nonlinear

/-! # Derivative `Ĥ^s → Ĥ^{s-1}` and the Navier–Stokes nonlinearity on `Ĥ^s`

For `s ≥ 3`, `N(u) = ℙ ∇·(u ⊗ u)` maps `Ĥ^s` to `Ĥ^{s-1}` and satisfies the tame bound
`‖N(u)‖_{Ĥ^{s-1}} ≤ 18 C_s ‖u‖_{Ĥ^s} ‖u‖_{Ĥ³}`, together with a Lipschitz estimate
sufficient for continuity along bounded `Ĥ^s` curves. -/

open MeasureTheory Real Filter Topology
open scoped ENNReal Convolution

set_option autoImplicit false

noncomputable section
namespace NonlinearHm

open LerayHeat SobolevFourier SobolevHilbert ProductEstimate
open ProductHm
open Nonlinear (Lij opNorm_Lij_le derivSym derivSym_apply derivSym_meas
  derivSym_opNorm_le enorm_derivSym_sq_le)

/-! ## Weight identity `sobW s · a ≤ sobW (s+1)` -/

lemma sobW_mul_a (s : ℕ) (ξ : E3) :
    sobW s ξ * (∑ i : Fin 3, ‖sym i ξ‖ₑ ^ 2) ≤ sobW (s + 1) ξ := by
  set a := ∑ i : Fin 3, ‖sym i ξ‖ₑ ^ 2
  have hmul : (∑ k ∈ Finset.range (s + 1), a ^ k) * a =
      ∑ k ∈ Finset.range (s + 1), a ^ (k + 1) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (pow_succ a k).symm
  have hexp : sobW (s + 1) ξ =
      (∑ k ∈ Finset.range (s + 1), a ^ (k + 1)) + 1 := by
    change ∑ k ∈ Finset.range (s + 2), a ^ k = _
    rw [Finset.sum_range_succ' (fun k => a ^ k) (s + 1), pow_zero]
  calc sobW s ξ * a
      = ∑ k ∈ Finset.range (s + 1), a ^ (k + 1) := hmul
    _ ≤ (∑ k ∈ Finset.range (s + 1), a ^ (k + 1)) + 1 := le_self_add
    _ = sobW (s + 1) ξ := hexp.symm

lemma bound_deriv (s : ℕ) (j : Fin 3) (ξ : E3) :
    sobW s ξ * ‖derivSym j ξ‖ₑ ^ 2 ≤ ENNReal.ofReal 1 * sobW (s + 1) ξ := by
  rw [ENNReal.ofReal_one, one_mul]
  have h1 : sobW s ξ * ‖derivSym j ξ‖ₑ ^ 2 ≤
      sobW s ξ * (∑ i : Fin 3, ‖sym i ξ‖ₑ ^ 2) :=
    mul_le_mul_of_nonneg_left (enorm_derivSym_sq_le j ξ) (zero_le _)
  exact h1.trans (sobW_mul_a s ξ)

lemma bound_deriv_pred {s : ℕ} (hs : 1 ≤ s) (j : Fin 3) (ξ : E3) :
    sobW (s - 1) ξ * ‖derivSym j ξ‖ₑ ^ 2 ≤ ENNReal.ofReal 1 * sobW s ξ := by
  have h := bound_deriv (s - 1) j ξ
  rwa [Nat.sub_add_cancel hs] at h

/-- **Derivative** `∂/∂xⱼ : Ĥ^s → Ĥ^{s-1}` for `s ≥ 1`. -/
def dH {s : ℕ} (hs : 1 ≤ s) (j : Fin 3) : Hm s →L[ℂ] Hm (s - 1) :=
  wmul (derivSym j) (derivSym_meas j) 1 zero_le_one (bound_deriv_pred hs j)

lemma norm_dH_le {s : ℕ} (hs : 1 ≤ s) (j : Fin 3) (G : Hm s) : ‖dH hs j G‖ ≤ ‖G‖ := by
  simpa using norm_wmul_le (derivSym j) (derivSym_meas j) 1 zero_le_one
    (bound_deriv_pred hs j) G

lemma one_le_of_three {s : ℕ} (hs : 3 ≤ s) : 1 ≤ s := le_trans (by norm_num : 1 ≤ 3) hs

lemma norm_incl_le {m m' : ℕ} (h : m' ≤ m) (F : Hm m) : ‖incl h F‖ ≤ ‖F‖ := by
  unfold incl
  have hnm := norm_wmul_le (fun _ => ContinuousLinearMap.id ℂ V) (fun g hg => hg)
    1 zero_le_one (fun ξ => by
      calc sobW m' ξ * ‖ContinuousLinearMap.id ℂ V‖ₑ ^ 2 ≤ sobW m' ξ * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
            have := enorm_sq_le_of_norm_le zero_le_one
              (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := V))
            simpa using this
        _ ≤ ENNReal.ofReal 1 * sobW m ξ := by simpa using sobW_mono h ξ) F
  simpa [Real.sqrt_one] using hnm

/-! ## Bilinearity of the `Ĥ^s` product -/

section Bilinear
variable (L : V →L[ℂ] V →L[ℂ] V)

lemma mulF_add_left {s : ℕ} (hs : 3 ≤ s) (F₁ F₂ G : Hm s) :
    mulF L hs (F₁ + F₂) G = mulF L hs F₁ G + mulF L hs F₂ G := by
  refine Lp.ext ?_
  have hE := (ac_μw s).ae_le
    ((integrable_of_Hm_ge3 hs F₁).ae_convolution_exists L (integrable_of_Hm_ge3 hs G))
  have hE' := (ac_μw s).ae_le
    ((integrable_of_Hm_ge3 hs F₂).ae_convolution_exists L (integrable_of_Hm_ge3 hs G))
  have hsum := (ac_vol s).ae_le (Lp.coeFn_add F₁ F₂)
  filter_upwards [coeFn_mulF L hs (F₁ + F₂) G, Lp.coeFn_add (mulF L hs F₁ G) (mulF L hs F₂ G),
    coeFn_mulF L hs F₁ G, coeFn_mulF L hs F₂ G, hE, hE'] with ξ h2 h3 h4 h5 hE hE'
  rw [h2, h3, Pi.add_apply, h4, h5, ← ConvolutionExistsAt.add_distrib hE hE']
  refine integral_congr_ae ?_
  filter_upwards [hsum] with η hη
  rw [hη, Pi.add_apply, L.map_add₂]

lemma mulF_add_right {s : ℕ} (hs : 3 ≤ s) (F G₁ G₂ : Hm s) :
    mulF L hs F (G₁ + G₂) = mulF L hs F G₁ + mulF L hs F G₂ := by
  refine Lp.ext ?_
  have hE := (ac_μw s).ae_le
    ((integrable_of_Hm_ge3 hs F).ae_convolution_exists L (integrable_of_Hm_ge3 hs G₁))
  have hE' := (ac_μw s).ae_le
    ((integrable_of_Hm_ge3 hs F).ae_convolution_exists L (integrable_of_Hm_ge3 hs G₂))
  have hsum := (ac_vol s).ae_le (Lp.coeFn_add G₁ G₂)
  filter_upwards [coeFn_mulF L hs F (G₁ + G₂), Lp.coeFn_add (mulF L hs F G₁) (mulF L hs F G₂),
    coeFn_mulF L hs F G₁, coeFn_mulF L hs F G₂, hE, hE'] with ξ h2 h3 h4 h5 hE hE'
  rw [h2, h3, Pi.add_apply, h4, h5, ← ConvolutionExistsAt.distrib_add hE hE']
  refine integral_congr_ae ?_
  filter_upwards [(quasiMeasurePreserving_sub_left_of_right_invariant
      (volume : Measure E3) ξ).ae hsum] with η hη
  rw [hη, Pi.add_apply, map_add]

lemma mulF_smul_left {s : ℕ} (hs : 3 ≤ s) (c : ℂ) (F G : Hm s) :
    mulF L hs (c • F) G = c • mulF L hs F G := by
  refine Lp.ext ?_
  have hsm := (ac_vol s).ae_le (Lp.coeFn_smul c F)
  filter_upwards [coeFn_mulF L hs (c • F) G, Lp.coeFn_smul c (mulF L hs F G),
    coeFn_mulF L hs F G] with ξ h2 h3 h4
  rw [h2, h3, Pi.smul_apply, h4]
  simp only [convolution_def]
  rw [← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [hsm] with η hη
  rw [hη, Pi.smul_apply, L.map_smul₂]

lemma mulF_smul_right {s : ℕ} (hs : 3 ≤ s) (c : ℂ) (F G : Hm s) :
    mulF L hs F (c • G) = c • mulF L hs F G := by
  refine Lp.ext ?_
  have hsm := (ac_vol s).ae_le (Lp.coeFn_smul c G)
  filter_upwards [coeFn_mulF L hs F (c • G), Lp.coeFn_smul c (mulF L hs F G),
    coeFn_mulF L hs F G] with ξ h2 h3 h4
  rw [h2, h3, Pi.smul_apply, h4]
  simp only [convolution_def]
  rw [← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [(quasiMeasurePreserving_sub_left_of_right_invariant
      (volume : Measure E3) ξ).ae hsm] with η hη
  rw [hη, Pi.smul_apply, map_smul]

lemma mulF_sub_left {s : ℕ} (hs : 3 ≤ s) (F₁ F₂ G : Hm s) :
    mulF L hs (F₁ - F₂) G = mulF L hs F₁ G - mulF L hs F₂ G := by
  have e : F₁ - F₂ = F₁ + ((-1 : ℂ) • F₂) := by rw [sub_eq_add_neg, ← neg_one_smul ℂ]
  rw [e, mulF_add_left, mulF_smul_left, neg_one_smul, sub_eq_add_neg]

lemma mulF_sub_right {s : ℕ} (hs : 3 ≤ s) (F G₁ G₂ : Hm s) :
    mulF L hs F (G₁ - G₂) = mulF L hs F G₁ - mulF L hs F G₂ := by
  have e : G₁ - G₂ = G₁ + ((-1 : ℂ) • G₂) := by rw [sub_eq_add_neg, ← neg_one_smul ℂ]
  rw [e, mulF_add_right, mulF_smul_right, neg_one_smul, sub_eq_add_neg]

theorem mulF_quad_sub {s : ℕ} (hs : 3 ≤ s) (F G : Hm s) :
    mulF L hs F F - mulF L hs G G = mulF L hs (F - G) F + mulF L hs G (F - G) := by
  rw [mulF_sub_left, mulF_sub_right]
  abel

/-- Tame Lipschitz bound for the quadratic map `F ↦ F ⋆[L] F` on `Ĥ^s`. -/
theorem norm_mulF_quad_sub_le {s : ℕ} (hs : 3 ≤ s) (F G : Hm s) :
    ‖mulF L hs F F - mulF L hs G G‖ ≤
      Cm s * ‖L‖ * ((‖F - G‖ * ‖incl hs F‖ + ‖incl hs (F - G)‖ * ‖F‖) +
        (‖G‖ * ‖incl hs (F - G)‖ + ‖incl hs G‖ * ‖F - G‖)) := by
  rw [mulF_quad_sub]
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_mulF_le L hs (F - G) F
  have h2 := norm_mulF_le L hs G (F - G)
  have hL : 0 ≤ ‖L‖ := ContinuousLinearMap.opNorm_nonneg L
  nlinarith [h1, h2, Cm_nonneg s, hL, norm_nonneg (F - G), norm_nonneg F, norm_nonneg G,
    norm_nonneg (incl hs F), norm_nonneg (incl hs G), norm_nonneg (incl hs (F - G))]

end Bilinear

/-! ## The nonlinearity `N(u) = ℙ ∇·(u ⊗ u)` on `Ĥ^s` -/

lemma mulF_Lij_norm_le {s : ℕ} (hs : 3 ≤ s) (i j : Fin 3) (u : Hm s) :
    ‖mulF (Lij i j) hs u u‖ ≤ Cm s * (‖u‖ * ‖incl hs u‖ + ‖incl hs u‖ * ‖u‖) := by
  refine (norm_mulF_le (Lij i j) hs u u).trans ?_
  have hL := opNorm_Lij_le i j
  have hC : 0 ≤ Cm s := Cm_nonneg s
  have hsum : 0 ≤ ‖u‖ * ‖incl hs u‖ + ‖incl hs u‖ * ‖u‖ :=
    add_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  calc Cm s * ‖Lij i j‖ * (‖u‖ * ‖incl hs u‖ + ‖incl hs u‖ * ‖u‖)
      ≤ Cm s * 1 * (‖u‖ * ‖incl hs u‖ + ‖incl hs u‖ * ‖u‖) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL hC) hsum
    _ = Cm s * (‖u‖ * ‖incl hs u‖ + ‖incl hs u‖ * ‖u‖) := by ring

lemma mulF_Lij_quad_sub_le {s : ℕ} (hs : 3 ≤ s) (i j : Fin 3) (u v : Hm s) :
    ‖mulF (Lij i j) hs u u - mulF (Lij i j) hs v v‖ ≤
      Cm s * ((‖u - v‖ * ‖incl hs u‖ + ‖incl hs (u - v)‖ * ‖u‖) +
        (‖v‖ * ‖incl hs (u - v)‖ + ‖incl hs v‖ * ‖u - v‖)) := by
  refine (norm_mulF_quad_sub_le (Lij i j) hs u v).trans ?_
  have hL := opNorm_Lij_le i j
  have hC : 0 ≤ Cm s := Cm_nonneg s
  have hsum : 0 ≤ (‖u - v‖ * ‖incl hs u‖ + ‖incl hs (u - v)‖ * ‖u‖) +
      (‖v‖ * ‖incl hs (u - v)‖ + ‖incl hs v‖ * ‖u - v‖) := by
    positivity
  calc Cm s * ‖Lij i j‖ * _
      ≤ Cm s * 1 * _ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL hC) hsum
    _ = _ := by ring

/-- `∇·(u ⊗ u) = ∑_{i,j} ∂ⱼ(uᵢ uⱼ)` as an element of `Ĥ^{s-1}`. -/
def divTensor {s : ℕ} (hs : 3 ≤ s) (u : Hm s) : Hm (s - 1) :=
  ∑ i : Fin 3, ∑ j : Fin 3, dH (one_le_of_three hs) j (mulF (Lij i j) hs u u)

/-- **Navier–Stokes nonlinearity** `N(u) = ℙ ∇·(u ⊗ u) : Ĥ^s → Ĥ^{s-1}`. -/
def NSN {s : ℕ} (hs : 3 ≤ s) (u : Hm s) : Hm (s - 1) :=
  lerayH (s - 1) (divTensor hs u)

lemma norm_divTensor_le {s : ℕ} (hs : 3 ≤ s) (u : Hm s) :
    ‖divTensor hs u‖ ≤ 9 * Cm s * (‖u‖ * ‖incl hs u‖ + ‖incl hs u‖ * ‖u‖) := by
  unfold divTensor
  refine ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)).trans ?_
  have hterm : ∀ i j,
      ‖dH (one_le_of_three hs) j (mulF (Lij i j) hs u u)‖ ≤
        Cm s * (‖u‖ * ‖incl hs u‖ + ‖incl hs u‖ * ‖u‖) := fun i j =>
    (norm_dH_le (one_le_of_three hs) j _).trans (mulF_Lij_norm_le hs i j u)
  have : ∑ i : Fin 3, ∑ j : Fin 3,
      ‖dH (one_le_of_three hs) j (mulF (Lij i j) hs u u)‖ ≤
      ∑ _i : Fin 3, ∑ _j : Fin 3,
        Cm s * (‖u‖ * ‖incl hs u‖ + ‖incl hs u‖ * ‖u‖) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
  refine this.trans ?_
  simp [Finset.sum_const, Fintype.card_fin]
  ring_nf
  exact le_rfl

/-- **Tame bound**: `‖N(u)‖_{Ĥ^{s-1}} ≤ 18 C_s ‖u‖_{Ĥ^s} ‖u‖_{Ĥ³}`. -/
theorem norm_NSN_le {s : ℕ} (hs : 3 ≤ s) (u : Hm s) :
    ‖NSN hs u‖ ≤ 18 * Cm s * ‖u‖ * ‖incl hs u‖ := by
  have h := (norm_lerayH_le (s - 1) _).trans (norm_divTensor_le hs u)
  have he : ‖u‖ * ‖incl hs u‖ + ‖incl hs u‖ * ‖u‖ = 2 * ‖u‖ * ‖incl hs u‖ := by ring
  have : 9 * Cm s * (‖u‖ * ‖incl hs u‖ + ‖incl hs u‖ * ‖u‖) =
      18 * Cm s * ‖u‖ * ‖incl hs u‖ := by rw [he]; ring
  exact h.trans (le_of_eq this)

lemma divTensor_sub {s : ℕ} (hs : 3 ≤ s) (u v : Hm s) :
    divTensor hs u - divTensor hs v = ∑ i : Fin 3, ∑ j : Fin 3,
      dH (one_le_of_three hs) j
        (mulF (Lij i j) hs u u - mulF (Lij i j) hs v v) := by
  unfold divTensor
  simp only [map_sub, Finset.sum_sub_distrib]

theorem norm_NSN_sub_le {s : ℕ} (hs : 3 ≤ s) (u v : Hm s) :
    ‖NSN hs u - NSN hs v‖ ≤
      9 * Cm s * ((‖u - v‖ * ‖incl hs u‖ + ‖incl hs (u - v)‖ * ‖u‖) +
        (‖v‖ * ‖incl hs (u - v)‖ + ‖incl hs v‖ * ‖u - v‖)) := by
  have hL : NSN hs u - NSN hs v = lerayH (s - 1) (divTensor hs u - divTensor hs v) := by
    simp only [NSN, map_sub]
  rw [hL]
  refine (norm_lerayH_le (s - 1) _).trans ?_
  rw [divTensor_sub]
  refine ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)).trans ?_
  have hterm : ∀ i j,
      ‖dH (one_le_of_three hs) j
        (mulF (Lij i j) hs u u - mulF (Lij i j) hs v v)‖ ≤
        Cm s * ((‖u - v‖ * ‖incl hs u‖ + ‖incl hs (u - v)‖ * ‖u‖) +
          (‖v‖ * ‖incl hs (u - v)‖ + ‖incl hs v‖ * ‖u - v‖)) := fun i j =>
    (norm_dH_le (one_le_of_three hs) j _).trans (mulF_Lij_quad_sub_le hs i j u v)
  have : ∑ i : Fin 3, ∑ j : Fin 3,
      ‖dH (one_le_of_three hs) j
        (mulF (Lij i j) hs u u - mulF (Lij i j) hs v v)‖ ≤
      ∑ _i : Fin 3, ∑ _j : Fin 3,
        Cm s * ((‖u - v‖ * ‖incl hs u‖ + ‖incl hs (u - v)‖ * ‖u‖) +
          (‖v‖ * ‖incl hs (u - v)‖ + ‖incl hs v‖ * ‖u - v‖)) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
  refine this.trans ?_
  simp [Finset.sum_const, Fintype.card_fin]
  ring_nf
  exact le_rfl

/-- Cruder Lipschitz bound, using `‖incl w‖_{Ĥ³} ≤ ‖w‖_{Ĥ^s}`. -/
theorem norm_NSN_sub_le' {s : ℕ} (hs : 3 ≤ s) (u v : Hm s) :
    ‖NSN hs u - NSN hs v‖ ≤ 18 * Cm s * (‖u‖ + ‖v‖) * ‖u - v‖ := by
  refine (norm_NSN_sub_le hs u v).trans ?_
  have hC : 0 ≤ 9 * Cm s := mul_nonneg (by norm_num) (Cm_nonneg s)
  have hu : ‖incl hs u‖ ≤ ‖u‖ := norm_incl_le hs u
  have hv : ‖incl hs v‖ ≤ ‖v‖ := norm_incl_le hs v
  have hd : ‖incl hs (u - v)‖ ≤ ‖u - v‖ := norm_incl_le hs (u - v)
  have h1 : ‖u - v‖ * ‖incl hs u‖ + ‖incl hs (u - v)‖ * ‖u‖ +
      (‖v‖ * ‖incl hs (u - v)‖ + ‖incl hs v‖ * ‖u - v‖) ≤
      2 * (‖u‖ + ‖v‖) * ‖u - v‖ := by
    nlinarith [norm_nonneg u, norm_nonneg v, norm_nonneg (u - v), hu, hv, hd]
  have : 9 * Cm s * ((‖u - v‖ * ‖incl hs u‖ + ‖incl hs (u - v)‖ * ‖u‖) +
        (‖v‖ * ‖incl hs (u - v)‖ + ‖incl hs v‖ * ‖u - v‖)) ≤
      9 * Cm s * (2 * (‖u‖ + ‖v‖) * ‖u - v‖) :=
    mul_le_mul_of_nonneg_left h1 hC
  refine this.trans ?_
  ring_nf
  exact le_rfl

end NonlinearHm

#print axioms NonlinearHm.sobW_mul_a
#print axioms NonlinearHm.dH
#print axioms NonlinearHm.norm_dH_le
#print axioms NonlinearHm.mulF_quad_sub
#print axioms NonlinearHm.norm_mulF_quad_sub_le
#print axioms NonlinearHm.norm_NSN_le
#print axioms NonlinearHm.norm_NSN_sub_le
#print axioms NonlinearHm.norm_NSN_sub_le'
