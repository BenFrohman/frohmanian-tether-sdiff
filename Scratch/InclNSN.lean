import Scratch.PersistenceHm

/-! # Inclusion commutes with the `Ĥ^s` product and the NS nonlinearity

General-index versions of the `PersistenceHm` commutation lemmas, which
only treated the drop `Ĥ^{k+1} ↪ Ĥ³`. -/

open MeasureTheory Real Filter Topology
open scoped ENNReal Convolution

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
namespace InclNSN

open LerayHeat SobolevHilbert ProductHm NonlinearHm PersistenceHm
open Nonlinear (derivSym derivSym_meas derivSym_apply Lij)

lemma sub_one_le_sub_one {s s' : ℕ} (h : s' ≤ s) : s' - 1 ≤ s - 1 :=
  Nat.sub_le_sub_right h 1

lemma three_le_of_le {s s' : ℕ} (hs' : 3 ≤ s') (h : s' ≤ s) : 3 ≤ s :=
  le_trans hs' h

lemma one_le_of_le_three {s s' : ℕ} (hs' : 3 ≤ s') (h : s' ≤ s) : 1 ≤ s :=
  one_le_of_three (three_le_of_le hs' h)

/-- Pointwise identity for `dH`, isolated to keep later `isDefEq` work small. -/
lemma coeFn_dH {s : ℕ} (hs : 1 ≤ s) (j : Fin 3) (G : Hm s) :
    (dH hs j G : E3 → V) =ᵐ[μw (s - 1)]
      fun ξ => derivSym j ξ ((G : E3 → V) ξ) := by
  simpa [dH] using coeFn_wmul (derivSym j) (derivSym_meas j) 1 zero_le_one
    (bound_deriv_pred hs j) G

lemma coeFn_dH_ae_low {s s' : ℕ} (hs : 1 ≤ s) (_h : s' ≤ s) (j : Fin 3) (G : Hm s) :
    (dH hs j G : E3 → V) =ᵐ[μw (s' - 1)]
      fun ξ => derivSym j ξ ((G : E3 → V) ξ) :=
  (ac_ww (s - 1) (s' - 1)).ae_le (coeFn_dH hs j G)

/-- Inclusion commutes with the `Ĥ^s` product. -/
lemma incl_mulF_of_le {s s' : ℕ} (hs' : 3 ≤ s') (h : s' ≤ s)
    (L : V →L[ℂ] V →L[ℂ] V) (F G : Hm s) :
    incl h (mulF L (three_le_of_le hs' h) F G) =
      mulF L hs' (incl h F) (incl h G) := by
  refine Lp.ext ?_
  have hs : 3 ≤ s := three_le_of_le hs' h
  have hconvF := coeFn_incl_vol h F
  have hconvG := coeFn_incl_vol h G
  have hE := (ac_μw s').ae_le
    ((integrable_of_Hm_ge3 hs F).ae_convolution_exists L
      (integrable_of_Hm_ge3 hs G))
  filter_upwards [coeFn_incl h (mulF L hs F G),
    (ac_ww s s').ae_le (coeFn_mulF L hs F G),
    coeFn_mulF L hs' (incl h F) (incl h G),
    hE] with ξ h1 h2 h3 hE
  rw [h1, h2, h3]
  refine integral_congr_ae ?_
  filter_upwards [hconvF,
    (quasiMeasurePreserving_sub_left_of_right_invariant (volume : Measure E3) ξ).ae hconvG]
    with η hF hG
  rw [hF, hG]

/-- Inclusion commutes with a derivative `Ĥ^s → Ĥ^{s-1}`. -/
lemma incl_dH_of_le {s s' : ℕ} (hs' : 3 ≤ s') (h : s' ≤ s) (j : Fin 3) (G : Hm s) :
    incl (sub_one_le_sub_one h)
      (dH (one_le_of_le_three hs' h) j G) =
      dH (one_le_of_three hs') j (incl h G) := by
  refine Lp.ext ?_
  have hs1 : 1 ≤ s := one_le_of_le_three hs' h
  filter_upwards [coeFn_incl (sub_one_le_sub_one h) (dH hs1 j G),
    coeFn_dH_ae_low hs1 h j G,
    coeFn_dH (one_le_of_three hs') j (incl h G),
    (ac_ww s' (s' - 1)).ae_le (coeFn_incl h G)] with ξ h1 h2 h3 h4
  rw [h1, h2, h3, h4]

/-- Inclusion commutes with `∇·(u ⊗ u)`. -/
lemma incl_divTensor_of_le {s s' : ℕ} (hs' : 3 ≤ s') (h : s' ≤ s) (u : Hm s) :
    incl (sub_one_le_sub_one h)
      (divTensor (three_le_of_le hs' h) u) =
      divTensor hs' (incl h u) := by
  unfold divTensor
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [incl_dH_of_le hs' h j, incl_mulF_of_le hs' h (Nonlinear.Lij i j) u u]

/-- Inclusion commutes with the Navier–Stokes nonlinearity. -/
lemma incl_NSN_of_le {s s' : ℕ} (hs' : 3 ≤ s') (h : s' ≤ s) (u : Hm s) :
    incl (sub_one_le_sub_one h)
      (NSN (three_le_of_le hs' h) u) =
      NSN hs' (incl h u) := by
  unfold NSN
  rw [incl_lerayH (sub_one_le_sub_one h), incl_divTensor_of_le hs' h]

#print axioms InclNSN.incl_mulF_of_le
#print axioms InclNSN.incl_dH_of_le
#print axioms InclNSN.incl_divTensor_of_le
#print axioms InclNSN.incl_NSN_of_le

end InclNSN
