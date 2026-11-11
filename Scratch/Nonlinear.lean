import Scratch.ProductH3
import Scratch.DuhamelUp

/-! # Bilinear `Ĥ³` product: additivity, coordinate maps, derivative `Ĥ³ → Ĥ²`,
and the Navier–Stokes nonlinearity `N(u) = ℙ ∇·(u ⊗ u)` as a quadratic map `Ĥ³ → Ĥ²`. -/

open MeasureTheory Real Filter Topology
open scoped ENNReal Convolution

noncomputable section
namespace Nonlinear

open LerayHeat SobolevFourier SobolevHilbert ProductEstimate ProductH3 Duhamel DuhamelUp

section Bilinear
variable (L : V →L[ℂ] V →L[ℂ] V)

lemma ae_conv_exists (F G : Hm 3) :
    ∀ᵐ ξ, ConvolutionExistsAt (F : E3 → V) (G : E3 → V) ξ L volume :=
  (integrable_of_H3 F).ae_convolution_exists L (integrable_of_H3 G)

lemma mulF_add_left (F₁ F₂ G : Hm 3) :
    mulF L (F₁ + F₂) G = mulF L F₁ G + mulF L F₂ G := by
  refine Lp.ext ?_
  have hE := (ac_μw 3).ae_le ((integrable_of_H3 F₁).ae_convolution_exists L (integrable_of_H3 G))
  have hE' := (ac_μw 3).ae_le ((integrable_of_H3 F₂).ae_convolution_exists L (integrable_of_H3 G))
  have hsum := (ac_vol 3).ae_le (Lp.coeFn_add F₁ F₂)
  filter_upwards [coeFn_mulF L (F₁ + F₂) G, Lp.coeFn_add (mulF L F₁ G) (mulF L F₂ G),
    coeFn_mulF L F₁ G, coeFn_mulF L F₂ G, hE, hE'] with ξ h2 h3 h4 h5 hE hE'
  rw [h2, h3, Pi.add_apply, h4, h5, ← ConvolutionExistsAt.add_distrib hE hE']
  refine integral_congr_ae ?_
  filter_upwards [hsum] with η hη
  rw [hη, Pi.add_apply, L.map_add₂]

lemma mulF_add_right (F G₁ G₂ : Hm 3) :
    mulF L F (G₁ + G₂) = mulF L F G₁ + mulF L F G₂ := by
  refine Lp.ext ?_
  have hE := (ac_μw 3).ae_le ((integrable_of_H3 F).ae_convolution_exists L (integrable_of_H3 G₁))
  have hE' := (ac_μw 3).ae_le ((integrable_of_H3 F).ae_convolution_exists L (integrable_of_H3 G₂))
  have hsum := (ac_vol 3).ae_le (Lp.coeFn_add G₁ G₂)
  filter_upwards [coeFn_mulF L F (G₁ + G₂), Lp.coeFn_add (mulF L F G₁) (mulF L F G₂),
    coeFn_mulF L F G₁, coeFn_mulF L F G₂, hE, hE'] with ξ h2 h3 h4 h5 hE hE'
  rw [h2, h3, Pi.add_apply, h4, h5, ← ConvolutionExistsAt.distrib_add hE hE']
  refine integral_congr_ae ?_
  filter_upwards [(quasiMeasurePreserving_sub_left_of_right_invariant (volume : Measure E3) ξ).ae hsum]
    with η hη
  rw [hη, Pi.add_apply, map_add]

lemma mulF_smul_left (c : ℂ) (F G : Hm 3) : mulF L (c • F) G = c • mulF L F G := by
  refine Lp.ext ?_
  have hsm := (ac_vol 3).ae_le (Lp.coeFn_smul c F)
  filter_upwards [coeFn_mulF L (c • F) G, Lp.coeFn_smul c (mulF L F G), coeFn_mulF L F G]
    with ξ h2 h3 h4
  rw [h2, h3, Pi.smul_apply, h4]
  simp only [convolution_def]
  rw [← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [hsm] with η hη
  rw [hη, Pi.smul_apply, L.map_smul₂]

lemma mulF_smul_right (c : ℂ) (F G : Hm 3) : mulF L F (c • G) = c • mulF L F G := by
  refine Lp.ext ?_
  have hsm := (ac_vol 3).ae_le (Lp.coeFn_smul c G)
  filter_upwards [coeFn_mulF L F (c • G), Lp.coeFn_smul c (mulF L F G), coeFn_mulF L F G]
    with ξ h2 h3 h4
  rw [h2, h3, Pi.smul_apply, h4]
  simp only [convolution_def]
  rw [← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [(quasiMeasurePreserving_sub_left_of_right_invariant (volume : Measure E3) ξ).ae hsm]
    with η hη
  rw [hη, Pi.smul_apply, map_smul]

lemma mulF_sub_left (F₁ F₂ G : Hm 3) :
    mulF L (F₁ - F₂) G = mulF L F₁ G - mulF L F₂ G := by
  have e : F₁ - F₂ = F₁ + ((-1 : ℂ) • F₂) := by rw [sub_eq_add_neg, ← neg_one_smul ℂ]
  rw [e, mulF_add_left, mulF_smul_left, neg_one_smul, sub_eq_add_neg]

lemma mulF_sub_right (F G₁ G₂ : Hm 3) :
    mulF L F (G₁ - G₂) = mulF L F G₁ - mulF L F G₂ := by
  have e : G₁ - G₂ = G₁ + ((-1 : ℂ) • G₂) := by rw [sub_eq_add_neg, ← neg_one_smul ℂ]
  rw [e, mulF_add_right, mulF_smul_right, neg_one_smul, sub_eq_add_neg]

/-- Quadratic difference identity. -/
theorem mulF_quad_sub (F G : Hm 3) :
    mulF L F F - mulF L G G = mulF L (F - G) F + mulF L G (F - G) := by
  rw [mulF_sub_left, mulF_sub_right]
  abel

/-- Lipschitz bound for the quadratic map `F ↦ F ⋆[L] F`. -/
theorem norm_mulF_quad_sub_le (F G : Hm 3) :
    ‖mulF L F F - mulF L G G‖ ≤ Cstar * ‖L‖ * (‖F‖ + ‖G‖) * ‖F - G‖ := by
  rw [mulF_quad_sub]
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_mulF_le L (F - G) F
  have h2 := norm_mulF_le L G (F - G)
  have hL : 0 ≤ ‖L‖ := ContinuousLinearMap.opNorm_nonneg L
  have hC : 0 ≤ Cstar := Cstar_nonneg
  nlinarith [norm_nonneg (F - G), norm_nonneg F, norm_nonneg G, h1, h2]

end Bilinear

/-! ## Coordinate embeddings and the tensor bilinear maps `Lᵢⱼ` -/

/-- The `i`-th coordinate functional on `ℂ³`. -/
def coordCLM (i : Fin 3) : V →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => v i
      map_add' := fun _ _ => by simp
      map_smul' := fun _ _ => by simp }

lemma norm_coordCLM_apply (i : Fin 3) (v : V) : ‖coordCLM i v‖ ≤ ‖v‖ := by
  simpa [coordCLM] using PiLp.norm_apply_le v i

lemma opNorm_coordCLM_le (i : Fin 3) : ‖coordCLM i‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    rw [one_mul]; exact norm_coordCLM_apply i v

/-- The embedding `c ↦ c eᵢ`. -/
def embedCLM (i : Fin 3) : ℂ →L[ℂ] V :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c => PiLp.single 2 i c
      map_add' := fun x y => by
        ext k
        simp only [PiLp.add_apply, PiLp.single_apply]
        split_ifs <;> simp
      map_smul' := fun c x => by
        ext k
        simp only [PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
        split_ifs <;> simp }

lemma embedCLM_apply (i : Fin 3) (c : ℂ) : embedCLM i c = PiLp.single 2 i c := rfl

lemma norm_embedCLM_apply (i : Fin 3) (c : ℂ) : ‖embedCLM i c‖ = ‖c‖ := by
  simp [embedCLM, PiLp.norm_single]

/-- Bilinear map `(u, v) ↦ (uᵢ vⱼ) eᵢ`. -/
def Lij (i j : Fin 3) : V →L[ℂ] V →L[ℂ] V :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ (fun u v => embedCLM i (coordCLM i u * coordCLM j v))
      (fun u₁ u₂ v => by simp [add_mul])
      (fun c u v => by
        change embedCLM i (coordCLM i (c • u) * coordCLM j v) =
          c • embedCLM i (coordCLM i u * coordCLM j v)
        rw [map_smul, smul_mul_assoc, map_smul])
      (fun u v₁ v₂ => by simp [mul_add])
      (fun c u v => by
        change embedCLM i (coordCLM i u * coordCLM j (c • v)) =
          c • embedCLM i (coordCLM i u * coordCLM j v)
        rw [map_smul, mul_smul_comm, map_smul]))
    1 fun u v => by
      rw [LinearMap.mk₂_apply, one_mul, norm_embedCLM_apply, norm_mul]
      exact mul_le_mul (norm_coordCLM_apply i u) (norm_coordCLM_apply j v)
        (norm_nonneg _) (norm_nonneg _)

lemma Lij_apply (i j : Fin 3) (u v : V) : Lij i j u v = embedCLM i (coordCLM i u * coordCLM j v) :=
  rfl

lemma opNorm_Lij_le (i j : Fin 3) : ‖Lij i j‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg zero_le_one (norm_nonneg u)) fun v => ?_
  change ‖Lij i j u v‖ ≤ 1 * ‖u‖ * ‖v‖
  rw [Lij_apply, one_mul, norm_embedCLM_apply, norm_mul]
  exact mul_le_mul (norm_coordCLM_apply i u) (norm_coordCLM_apply j v)
    (norm_nonneg _) (norm_nonneg _)

/-! ## Derivative multiplier `Ĥ³ → Ĥ²` -/

/-- Fourier symbol of `∂/∂xⱼ`: multiplication by `2πi ξⱼ`. -/
def derivSym (j : Fin 3) (ξ : E3) : V →L[ℂ] V := (sym j ξ) • ContinuousLinearMap.id ℂ V

lemma derivSym_apply (j : Fin 3) (ξ : E3) (v : V) : derivSym j ξ v = sym j ξ • v := rfl

lemma derivSym_meas (j : Fin 3) (g : E3 → V) (hg : AEStronglyMeasurable g) :
    AEStronglyMeasurable (fun ξ => derivSym j ξ (g ξ)) := by
  simp only [derivSym_apply]
  exact (measurable_sym j).aestronglyMeasurable.smul hg

lemma derivSym_opNorm_le (j : Fin 3) (ξ : E3) : ‖derivSym j ξ‖ ≤ ‖sym j ξ‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => by
    rw [derivSym_apply, norm_smul]

lemma enorm_derivSym_sq_le (j : Fin 3) (ξ : E3) :
    ‖derivSym j ξ‖ₑ ^ 2 ≤ ∑ i : Fin 3, ‖sym i ξ‖ₑ ^ 2 := by
  have h := derivSym_opNorm_le j ξ
  have : ‖derivSym j ξ‖ₑ ^ 2 ≤ ‖sym j ξ‖ₑ ^ 2 := by
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm (sym j ξ),
      ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) h 2)
  exact this.trans (Finset.single_le_sum (s := Finset.univ) (fun i _ => show 0 ≤ ‖sym i ξ‖ₑ ^ 2 from zero_le _)
    (Finset.mem_univ j))

lemma sobW2_mul_a_le (ξ : E3) :
    sobW 2 ξ * (∑ i : Fin 3, ‖sym i ξ‖ₑ ^ 2) ≤ sobW 3 ξ := by
  set a := ∑ i : Fin 3, ‖sym i ξ‖ₑ ^ 2
  have h2 : sobW 2 ξ = 1 + a + a ^ 2 := by
    change ∑ k ∈ Finset.range (2 + 1), a ^ k = 1 + a + a ^ 2
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [pow_zero, pow_one, add_zero]
    ac_rfl
  have h3 : sobW 3 ξ = 1 + a + a ^ 2 + a ^ 3 := by
    change ∑ k ∈ Finset.range (3 + 1), a ^ k = 1 + a + a ^ 2 + a ^ 3
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    simp only [pow_zero, pow_one, add_zero]
    ac_rfl
  rw [h2, h3]
  have e : (1 + a + a ^ 2) * a = a + a ^ 2 + a ^ 3 := by ring
  have e' : 1 + a + a ^ 2 + a ^ 3 = 1 + (a + a ^ 2 + a ^ 3) := by ac_rfl
  rw [e, e']
  exact le_add_self

lemma bound_deriv (j : Fin 3) (ξ : E3) :
    sobW 2 ξ * ‖derivSym j ξ‖ₑ ^ 2 ≤ ENNReal.ofReal 1 * sobW 3 ξ := by
  rw [ENNReal.ofReal_one, one_mul]
  refine (mul_le_mul_right (enorm_derivSym_sq_le j ξ) _).trans (sobW2_mul_a_le ξ)

/-- **Derivative** `∂/∂xⱼ : Ĥ³ → Ĥ²`. -/
def dH (j : Fin 3) : Hm 3 →L[ℂ] Hm 2 :=
  wmul (derivSym j) (derivSym_meas j) 1 zero_le_one (bound_deriv j)

lemma norm_dH_le (j : Fin 3) (G : Hm 3) : ‖dH j G‖ ≤ ‖G‖ := by
  simpa using norm_wmul_le (derivSym j) (derivSym_meas j) 1 zero_le_one (bound_deriv j) G

lemma mulF_Lij_norm_le (i j : Fin 3) (u : Hm 3) :
    ‖mulF (Lij i j) u u‖ ≤ Cstar * ‖u‖ ^ 2 := by
  refine (norm_mulF_le (Lij i j) u u).trans ?_
  have hL := opNorm_Lij_le i j
  calc Cstar * ‖Lij i j‖ * ‖u‖ * ‖u‖
      = Cstar * ‖Lij i j‖ * (‖u‖ * ‖u‖) := by ring
    _ ≤ Cstar * 1 * (‖u‖ * ‖u‖) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL Cstar_nonneg)
          (mul_nonneg (norm_nonneg u) (norm_nonneg u))
    _ = Cstar * ‖u‖ ^ 2 := by ring

lemma mulF_Lij_quad_sub_le (i j : Fin 3) (u v : Hm 3) :
    ‖mulF (Lij i j) u u - mulF (Lij i j) v v‖ ≤ Cstar * (‖u‖ + ‖v‖) * ‖u - v‖ := by
  refine (norm_mulF_quad_sub_le (Lij i j) u v).trans ?_
  have hL := opNorm_Lij_le i j
  calc Cstar * ‖Lij i j‖ * (‖u‖ + ‖v‖) * ‖u - v‖
      = Cstar * ‖Lij i j‖ * ((‖u‖ + ‖v‖) * ‖u - v‖) := by ring
    _ ≤ Cstar * 1 * ((‖u‖ + ‖v‖) * ‖u - v‖) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL Cstar_nonneg)
          (mul_nonneg (add_nonneg (norm_nonneg u) (norm_nonneg v)) (norm_nonneg (u - v)))
    _ = Cstar * (‖u‖ + ‖v‖) * ‖u - v‖ := by ring

/-! ## The nonlinearity `N(u) = ℙ ∇·(u ⊗ u)` -/

/-- `∇·(u ⊗ u) = ∑_{i,j} ∂ⱼ(uᵢ uⱼ)` as an element of `Ĥ²`. -/
def divTensor (u : Hm 3) : Hm 2 := ∑ i : Fin 3, ∑ j : Fin 3, dH j (mulF (Lij i j) u u)

/-- **Navier–Stokes nonlinearity** `N(u) = ℙ ∇·(u ⊗ u) : Ĥ³ → Ĥ²`. -/
def NSN (u : Hm 3) : Hm 2 := lerayH 2 (divTensor u)

lemma norm_divTensor_le (u : Hm 3) : ‖divTensor u‖ ≤ 9 * Cstar * ‖u‖ ^ 2 := by
  unfold divTensor
  refine ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)).trans ?_
  have hterm : ∀ i j, ‖dH j (mulF (Lij i j) u u)‖ ≤ Cstar * ‖u‖ ^ 2 := fun i j =>
    (norm_dH_le j _).trans (mulF_Lij_norm_le i j u)
  have : ∑ i : Fin 3, ∑ j : Fin 3, ‖dH j (mulF (Lij i j) u u)‖ ≤
      ∑ _i : Fin 3, ∑ _j : Fin 3, Cstar * ‖u‖ ^ 2 :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
  refine this.trans ?_
  simp [Finset.sum_const, Fintype.card_fin]
  ring_nf
  exact le_rfl

theorem norm_NSN_le (u : Hm 3) : ‖NSN u‖ ≤ 9 * Cstar * ‖u‖ ^ 2 :=
  (norm_lerayH_le 2 _).trans (norm_divTensor_le u)

lemma divTensor_sub (u v : Hm 3) :
    divTensor u - divTensor v = ∑ i : Fin 3, ∑ j : Fin 3,
      dH j (mulF (Lij i j) u u - mulF (Lij i j) v v) := by
  unfold divTensor
  simp only [map_sub, Finset.sum_sub_distrib]

theorem norm_NSN_sub_le (u v : Hm 3) :
    ‖NSN u - NSN v‖ ≤ 9 * Cstar * (‖u‖ + ‖v‖) * ‖u - v‖ := by
  have hL : NSN u - NSN v = lerayH 2 (divTensor u - divTensor v) := by
    simp only [NSN, map_sub]
  rw [hL]
  refine (norm_lerayH_le 2 _).trans ?_
  rw [divTensor_sub]
  refine ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)).trans ?_
  have hterm : ∀ i j, ‖dH j (mulF (Lij i j) u u - mulF (Lij i j) v v)‖ ≤
      Cstar * (‖u‖ + ‖v‖) * ‖u - v‖ := fun i j =>
    (norm_dH_le j _).trans (mulF_Lij_quad_sub_le i j u v)
  have : ∑ i : Fin 3, ∑ j : Fin 3, ‖dH j (mulF (Lij i j) u u - mulF (Lij i j) v v)‖ ≤
      ∑ _i : Fin 3, ∑ _j : Fin 3, Cstar * (‖u‖ + ‖v‖) * ‖u - v‖ :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
  refine this.trans ?_
  simp [Finset.sum_const, Fintype.card_fin]
  ring_nf
  exact le_rfl

end Nonlinear

#print axioms Nonlinear.mulF_add_left
#print axioms Nonlinear.mulF_quad_sub
#print axioms Nonlinear.norm_mulF_quad_sub_le
#print axioms Nonlinear.opNorm_Lij_le
#print axioms Nonlinear.dH
#print axioms Nonlinear.norm_dH_le
#print axioms Nonlinear.norm_NSN_le
#print axioms Nonlinear.norm_NSN_sub_le
