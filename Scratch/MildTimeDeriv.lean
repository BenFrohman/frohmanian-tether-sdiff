import Scratch.DuhamelDeriv
import Scratch.PersistenceHm
import Mathlib.Analysis.Calculus.Deriv.Add

/-! # Time derivative of a high-regularity mild path in a lower `Ĥ^m`

A mild path in `C([0,T]; Ĥ^{k+1})` is identified, after inclusion to `Ĥ^m`
(`m ≤ k`), with the same-space heat-plus-Duhamel formula.  Its right
derivative in `Ĥ^m` along `[t0, T]` then follows from `HeatDeriv` and
`DuhamelDeriv.hasDerivWithinAt_duhνSame_Ici`. -/

open MeasureTheory Real Filter Topology Set
open scoped ENNReal

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
namespace MildTimeDeriv

open LerayHeat SobolevHilbert Duhamel HeatDeriv MildExistence
  PersistenceHm DuhamelDeriv

/-- Inclusion of the smoothing `duhHigh` integral is the same-space `duhνSame`. -/
lemma incl_duhHigh_to_duhνSame {k : ℕ} (hk : 2 ≤ k) {m : ℕ} (hm : m ≤ k)
    {ν t : ℝ} (hνt : 0 ≤ ν * t)
    {G : ℝ → Hm k} (hG : Continuous G) :
    incl (hm.trans (Nat.le_succ k)) (duhHigh hk ν G t) =
      duhνSame m ν (fun s => incl hm (G s)) t := by
  unfold duhHigh
  cases pred_succ_eq hk
  trans incl hm (incl (Nat.le_succ k) (duhν k ν G t))
  · exact (incl_comp (Nat.le_succ k) hm (duhν k ν G t)).symm
  · rw [incl_duhν_to_duhνSame k hνt hG, incl_duhνSame_of_le hm ν hG]

/-- The extended nonlinearity of a mild path, as a map `ℝ → Ĥ^k`. -/
def nsnExt {k : ℕ} (hk : 2 ≤ k) {T : ℝ} (hT : 0 ≤ T) (u : XTs k T) : ℝ → Hm k :=
  fun s => NSNsucc hk (ContinuousMap.IccExtend hT u s)

lemma continuous_nsnExt {k : ℕ} (hk : 2 ≤ k) {T : ℝ} (hT : 0 ≤ T) (u : XTs k T) :
    Continuous (nsnExt hk hT u) :=
  continuous_NSN_extUS hk hT u

/-- The included mild path equals the same-space heat-plus-Duhamel formula. -/
lemma mildS_eq_duhνSame {k : ℕ} (hk : 2 ≤ k) {m : ℕ} (hm : m ≤ k)
    {T ν : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    {u₀ : Hm (k + 1)} {u : XTs k T} (hu : IsMildS hk hT ν u₀ u)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    incl (hm.trans (Nat.le_succ k)) (u ⟨t, ht⟩) =
      heatH m (ν * t) (incl (hm.trans (Nat.le_succ k)) u₀) -
        duhνSame m ν (fun s => incl hm (nsnExt hk hT u s)) t := by
  have hνt : 0 ≤ ν * t := mul_nonneg hν.le ht.1
  set hle := hm.trans (Nat.le_succ k)
  have hU : u ⟨t, ht⟩ =
      heatH (k + 1) (ν * t) u₀ - duhHigh hk ν (nsnExt hk hT u) t := by
    simpa [nsnExt] using hu ⟨t, ht⟩
  have hheat :
      incl hle (heatH (k + 1) (ν * t) u₀) =
        heatH m (ν * t) (incl hle u₀) :=
    incl_heatH_of_le hle (ν * t) u₀
  have hduh :
      incl hle (duhHigh hk ν (nsnExt hk hT u) t) =
        duhνSame m ν (fun s => incl hm (nsnExt hk hT u s)) t :=
    incl_duhHigh_to_duhνSame hk hm hνt (continuous_nsnExt hk hT u)
  rw [hU, map_sub, hheat, hduh]

#print axioms MildTimeDeriv.incl_duhHigh_to_duhνSame
#print axioms MildTimeDeriv.mildS_eq_duhνSame

end MildTimeDeriv
