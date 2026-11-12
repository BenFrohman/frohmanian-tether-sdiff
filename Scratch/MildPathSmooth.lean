import Scratch.MildTimeDeriv
import Scratch.NonlinearSmooth
import Scratch.InclNSN
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! # Higher time-regularity of an included mild path

Once the path is known to be `C¹` in every `Ĥ^m` with two spare
derivatives, the identity `∂t u = ν Δu - N(u)` together with `C^∞` of
`N` bootstraps to `C^n` in `Ĥ^m` whenever `m + 2n ≤ k`. -/

open MeasureTheory Real Filter Topology Set
open scoped ENNReal

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
namespace MildPathSmooth

open LerayHeat SobolevHilbert PersistenceHm Duhamel HeatDeriv
  MildExistence DuhamelDeriv MildTimeDeriv NonlinearHm
  NonlinearSmooth InclNSN

/-- Transport of an `Ĥ^a` representative along an index equality does not
change the underlying function. Isolated so `subst` can eliminate a
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

/-- Inclusion of `NSNsucc` is inclusion of `NSN` at the predecessor index. -/
lemma incl_NSNsucc {k m : ℕ} (hk : 2 ≤ k) (hm : m ≤ k) (v : Hm (k + 1)) :
    incl hm (NSNsucc hk v) =
      incl (by simpa [Nat.add_sub_cancel] using hm) (NSN (three_le_succ hk) v) := by
  refine Lp.ext ?_
  filter_upwards [ProductHm.coeFn_incl hm (NSNsucc hk v),
    ProductHm.coeFn_incl (by simpa [Nat.add_sub_cancel] using hm) (NSN (three_le_succ hk) v),
    (ac_ww k m).ae_le (coeFn_NSNsucc hk v)] with ξ h1 h2 h3
  rw [h1, h2, h3]

lemma le_succ_succ {m k : ℕ} (hm : m ≤ k) : m + 1 ≤ k + 1 :=
  Nat.succ_le_succ hm


#print axioms MildPathSmooth.coeFn_eq_rec_Hm
#print axioms MildPathSmooth.coeFn_NSNsucc
#print axioms MildPathSmooth.incl_NSNsucc

end MildPathSmooth
