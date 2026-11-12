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

/-- Transport of an `Ĥ^a` representative along an index equality does not
change the underlying function. Isolated so `cases` can eliminate a
free index. -/
lemma coeFn_eq_rec_Hm {a b : ℕ} (e : a = b) (v : Hm a) :
    ((e ▸ v : Hm b) : E3 → V) =ᵐ[μw b] (v : E3 → V) := by
  cases e
  exact Filter.Eventually.of_forall fun _ => rfl

/-- The underlying function of `NSNsucc` agrees with `NSN`. -/
lemma coeFn_NSNsucc {k : ℕ} (hk : 2 ≤ k) (v : Hm (k + 1)) :
    (NSNsucc hk v : E3 → V) =ᵐ[μw k] (NSN (three_le_succ hk) v : E3 → V) := by
  unfold NSNsucc
  exact coeFn_eq_rec_Hm (Nat.add_sub_cancel k 1) (NSN (three_le_succ hk) v)

/-- Inclusion is independent of the inequality proof. -/
lemma incl_irrel {m m' : ℕ} (h1 h2 : m' ≤ m) (F : Hm m) :
    incl h1 F = incl h2 F := by
  refine Lp.ext ?_
  filter_upwards [ProductHm.coeFn_incl h1 F, ProductHm.coeFn_incl h2 F] with ξ a b
  exact a.trans b.symm

/-- Inclusion of `NSNsucc` is inclusion of `NSN` at the predecessor index. -/
lemma incl_NSNsucc {k m : ℕ} (hk : 2 ≤ k) (hm : m ≤ k) (v : Hm (k + 1)) :
    incl hm (NSNsucc hk v) =
      incl (by simpa [Nat.add_sub_cancel] using hm) (NSN (three_le_succ hk) v) := by
  refine Lp.ext ?_
  filter_upwards [ProductHm.coeFn_incl hm (NSNsucc hk v),
    ProductHm.coeFn_incl (by simpa [Nat.add_sub_cancel] using hm)
      (NSN (three_le_succ hk) v),
    (ac_ww k m).ae_le (coeFn_NSNsucc hk v)] with ξ h1 h2 h3
  rw [h1, h2, h3]

lemma le_succ_succ {m k : ℕ} (hm : m ≤ k) : m + 1 ≤ k + 1 :=
  Nat.succ_le_succ hm

lemma le_of_add_two_le {m k : ℕ} (hm2 : m + 2 ≤ k) : m ≤ k :=
  (Nat.le_add_right m 2).trans hm2

/-- The inequality proof is irrelevant for `NSN`. -/
lemma NSN_irrel {s : ℕ} (h1 h2 : 3 ≤ s) (u : Hm s) : NSN h1 u = NSN h2 u := by
  rw [Subsingleton.elim h1 h2]

/-- Pointwise, `N(u)` and `N(incl u)` agree after inclusion. -/
lemma coeFn_NSN_incl_of_le {s s' : ℕ} (hs' : 3 ≤ s') (h : s' ≤ s) (u : Hm s) :
    (NSN (three_le_of_le hs' h) u : E3 → V)
      =ᵐ[μw (s' - 1)] (NSN hs' (incl h u) : E3 → V) := by
  have hNSN := incl_NSN_of_le hs' h u
  have hincl := ProductHm.coeFn_incl (sub_one_le_sub_one h)
    (NSN (three_le_of_le hs' h) u)
  have hfun : (incl (sub_one_le_sub_one h) (NSN (three_le_of_le hs' h) u) : E3 → V)
      =ᵐ[μw (s' - 1)] (NSN hs' (incl h u) : E3 → V) :=
    Filter.Eventually.of_forall fun ξ =>
      congrArg (fun z : Hm (s' - 1) => (z : E3 → V) ξ) hNSN
  exact hincl.symm.trans hfun

/-- The `(m+1)-1` transport packaged as in `NSNsucc`: including `NSNsucc`
from the high space equals `NSNsucc` of the included field, both as
values in `Ĥ^m`. -/
lemma incl_incl_NSNsucc
    {k m : ℕ} (hk : 2 ≤ k) (hm : 2 ≤ m) (hm2 : m + 2 ≤ k) (v : Hm (k + 1)) :
    incl (Nat.le_add_right m 2) (incl hm2 (NSNsucc hk v)) =
      NSNsucc hm (incl (le_succ_succ (le_of_add_two_le hm2)) v) := by
  refine Lp.ext ?_
  have hsucc : m + 1 ≤ k + 1 := le_succ_succ (le_of_add_two_le hm2)
  have hLinc1 := ProductHm.coeFn_incl (Nat.le_add_right m 2)
    (incl hm2 (NSNsucc hk v))
  have hLinc2 := (ac_ww (m + 2) m).ae_le
    (ProductHm.coeFn_incl hm2 (NSNsucc hk v))
  have hL := (ac_ww k m).ae_le (coeFn_NSNsucc hk v)
  have hR := coeFn_NSNsucc hm (incl hsucc v)
  have hRel := (ac_ww (m + 1 - 1) m).ae_le
    (coeFn_NSN_incl_of_le (three_le_succ hm) hsucc v)
  have hIr :
      NSN (three_le_succ hk) v =
        NSN (three_le_of_le (three_le_succ hm) hsucc) v :=
    NSN_irrel _ _ v
  filter_upwards [hLinc1, hLinc2, hL, hR, hRel] with ξ a b c d e
  exact a.trans (b.trans (c.trans
    ((congrArg (fun z : Hm (k + 1 - 1) => (z : E3 → V) ξ) hIr).trans
      (e.trans d.symm))))

#print axioms InclNSN.coeFn_NSNsucc
#print axioms InclNSN.incl_NSNsucc
#print axioms InclNSN.incl_incl_NSNsucc

end InclNSN
