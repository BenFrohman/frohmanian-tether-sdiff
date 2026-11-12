import Scratch.NonlinearHm
import Scratch.PersistenceHm
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # `C^∞` regularity of the Navier–Stokes nonlinearity on `Ĥ^s`

The product `mulF` is a bounded bilinear map on `Ĥ^s` (`s ≥ 3`), hence
`C^∞`.  The projected divergence `N(u) = ℙ ∇·(u ⊗ u)` is a composition of
this quadratic map with continuous linear maps, so it is `C^∞` as a map
`Ĥ^s → Ĥ^{s-1}`. -/

open MeasureTheory Real Filter Topology
open scoped ENNReal

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
namespace NonlinearSmooth

open LerayHeat SobolevHilbert ProductHm NonlinearHm PersistenceHm

/-- Real scalar action on `ℂ` agrees with multiplication by `↑c`. -/
lemma real_smul_eq_coe_smul_complex (c : ℝ) (z : ℂ) : c • z = (c : ℂ) • z := by
  simp [smul_eq_mul]

/-- Real scalar action on `V` agrees with the complex action of `↑c`. -/
lemma real_smul_eq_coe_smul_V (c : ℝ) (v : V) : c • v = (c : ℂ) • v := by
  ext i
  simp only [PiLp.smul_apply]
  exact real_smul_eq_coe_smul_complex c (v i)

/-- Real scalar action on `Ĥ^s` agrees with the complex action of `↑c`. -/
lemma real_smul_eq_coe_smul {s : ℕ} (c : ℝ) (F : Hm s) : c • F = (c : ℂ) • F := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_smul c F, Lp.coeFn_smul (c : ℂ) F] with ξ h1 h2
  rw [h1, h2]
  exact real_smul_eq_coe_smul_V c ((F : E3 → V) ξ)

/-- A `ℂ`-linear continuous map is a bounded linear map over `ℝ`. -/
lemma isBoundedLinearMap_restrictCLM {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    (f : E →L[ℂ] F)
    (hE : ∀ (c : ℝ) (x : E), c • x = (c : ℂ) • x)
    (hF : ∀ (c : ℝ) (y : F), c • y = (c : ℂ) • y) :
    IsBoundedLinearMap ℝ (fun x => f x) where
  map_add := f.map_add
  map_smul := fun c x => by rw [hE, hF, map_smul]
  bound :=
    ⟨max ‖f‖ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x =>
      (f.le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg x))⟩

/-- The `Ĥ^s` product is a bounded bilinear map over `ℝ`.  The tame estimate
`‖F ⋆ G‖_s ≤ C_s ‖L‖ (‖F‖_s ‖G‖_3 + ‖F‖_3 ‖G‖_s)` upgrades to a Banach
bilinear bound via `‖incl F‖ ≤ ‖F‖`. -/
lemma isBoundedBilinear_mulF {s : ℕ} (hs : 3 ≤ s) (L : V →L[ℂ] V →L[ℂ] V) :
    IsBoundedBilinearMap ℝ (fun p : Hm s × Hm s => mulF L hs p.1 p.2) where
  add_left F₁ F₂ G := mulF_add_left L hs F₁ F₂ G
  smul_left c F G := by
    rw [real_smul_eq_coe_smul, real_smul_eq_coe_smul]
    exact mulF_smul_left L hs (c : ℂ) F G
  add_right F G₁ G₂ := mulF_add_right L hs F G₁ G₂
  smul_right c F G := by
    rw [real_smul_eq_coe_smul, real_smul_eq_coe_smul]
    exact mulF_smul_right L hs (c : ℂ) F G
  bound := by
    refine ⟨max (2 * Cm s * ‖L‖) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
    intro F G
    have h := norm_mulF_le L hs F G
    have hC : 0 ≤ Cm s := Cm_nonneg s
    have hL : 0 ≤ ‖L‖ := ContinuousLinearMap.opNorm_nonneg L
    have hbound : ‖mulF L hs F G‖ ≤ 2 * Cm s * ‖L‖ * ‖F‖ * ‖G‖ := by
      refine h.trans ?_
      have h1 : ‖incl hs G‖ ≤ ‖G‖ := norm_incl_le hs G
      have h2 : ‖incl hs F‖ ≤ ‖F‖ := norm_incl_le hs F
      have : ‖F‖ * ‖incl hs G‖ + ‖incl hs F‖ * ‖G‖ ≤ ‖F‖ * ‖G‖ + ‖F‖ * ‖G‖ :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (norm_nonneg F))
          (mul_le_mul_of_nonneg_right h2 (norm_nonneg G))
      calc Cm s * ‖L‖ * (‖F‖ * ‖incl hs G‖ + ‖incl hs F‖ * ‖G‖)
          ≤ Cm s * ‖L‖ * (‖F‖ * ‖G‖ + ‖F‖ * ‖G‖) :=
            mul_le_mul_of_nonneg_left this (mul_nonneg hC hL)
        _ = 2 * Cm s * ‖L‖ * ‖F‖ * ‖G‖ := by ring
    have hC2 : 2 * Cm s * ‖L‖ ≤ max (2 * Cm s * ‖L‖) 1 := le_max_left _ _
    exact hbound.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC2 (norm_nonneg F)) (norm_nonneg G))

/-- The uncurried product is `C^∞` as a map of two `Ĥ^s` arguments. -/
theorem contDiff_mulF {s : ℕ} (hs : 3 ≤ s) (L : V →L[ℂ] V →L[ℂ] V) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun p : Hm s × Hm s => mulF L hs p.1 p.2) :=
  (isBoundedBilinear_mulF hs L).contDiff

/-- The quadratic map `u ↦ u ⋆[L] u` is `C^∞` on `Ĥ^s`. -/
theorem contDiff_mulF_quad {s : ℕ} (hs : 3 ≤ s) (L : V →L[ℂ] V →L[ℂ] V) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun u : Hm s => mulF L hs u u) :=
  (contDiff_mulF hs L).comp (contDiff_id.prodMk contDiff_id)

/-- `∇·(u ⊗ u)` is `C^∞` as a map `Ĥ^s → Ĥ^{s-1}`. -/
theorem contDiff_divTensor {s : ℕ} (hs : 3 ≤ s) {n : WithTop ℕ∞} :
    ContDiff ℝ n (divTensor (s := s) hs) := by
  unfold divTensor
  refine ContDiff.sum (s := Finset.univ) fun i _ =>
    ContDiff.sum (s := Finset.univ) fun j _ => ?_
  exact (isBoundedLinearMap_restrictCLM (dH (one_le_of_three hs) j)
      real_smul_eq_coe_smul real_smul_eq_coe_smul).contDiff.comp
    (contDiff_mulF_quad hs (Nonlinear.Lij i j))

/-- The Navier–Stokes nonlinearity `N : Ĥ^s → Ĥ^{s-1}` is `C^∞`. -/
theorem contDiff_NSN {s : ℕ} (hs : 3 ≤ s) {n : WithTop ℕ∞} :
    ContDiff ℝ n (NSN (s := s) hs) :=
  (isBoundedLinearMap_restrictCLM (lerayH (s - 1))
      real_smul_eq_coe_smul real_smul_eq_coe_smul).contDiff.comp
    (contDiff_divTensor hs)

/-- The nonlinearity as a map `Ĥ^{k+1} → Ĥ^k` is `C^∞`. -/
theorem contDiff_NSNsucc {k : ℕ} (hk : 2 ≤ k) {n : WithTop ℕ∞} :
    ContDiff ℝ n (NSNsucc hk) := by
  unfold NSNsucc
  exact Eq.rec
    (motive := fun (m : ℕ) (h : k + 1 - 1 = m) =>
      ContDiff ℝ n (fun u : Hm (k + 1) => h ▸ NSN (three_le_succ hk) u))
    (contDiff_NSN (three_le_succ hk) (n := n)) (Nat.add_sub_cancel k 1)

#print axioms NonlinearSmooth.isBoundedBilinear_mulF
#print axioms NonlinearSmooth.contDiff_mulF
#print axioms NonlinearSmooth.contDiff_mulF_quad
#print axioms NonlinearSmooth.contDiff_divTensor
#print axioms NonlinearSmooth.contDiff_NSN
#print axioms NonlinearSmooth.contDiff_NSNsucc

end NonlinearSmooth
