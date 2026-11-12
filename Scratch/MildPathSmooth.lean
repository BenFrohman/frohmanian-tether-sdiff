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
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

noncomputable section
namespace MildPathSmooth

open LerayHeat SobolevHilbert PersistenceHm Duhamel HeatDeriv
  MildExistence DuhamelDeriv MildTimeDeriv NonlinearHm
  NonlinearSmooth InclNSN

lemma inclExt_irrel {k m : ℕ} (h1 h2 : m ≤ k + 1) {T : ℝ} (hT : 0 ≤ T)
    (u : XTs k T) : inclExt h1 hT u = inclExt h2 hT u :=
  funext fun _ => incl_irrel h1 h2 _

/-- The `N`-term of the included mild path is `NSNsucc` of the path in
`Ĥ^{m+1}`, packaged as a value in `Ĥ^m`. -/
lemma incl_nsnExt_eq_NSNsucc
    {k : ℕ} (hk : 2 ≤ k) {m : ℕ} (hm : 2 ≤ m) (hm2 : m + 2 ≤ k)
    {T : ℝ} (hT : 0 ≤ T) (u : XTs k T) (t : ℝ) :
    incl (incl_le_add_two m) (incl hm2 (nsnExt hk hT u t)) =
      NSNsucc hm (inclExt (le_succ_succ (InclNSN.le_of_add_two_le hm2)) hT u t) := by
  unfold nsnExt inclExt
  rw [← incl_incl_NSNsucc hk hm hm2]

/-- The time derivative of the included mild path is `ν Δu - N(u)` in
`Ĥ^m`, with the nonlinearity written as `NSNsucc`. -/
theorem mildSDeriv_eq_NSNsucc
    {k : ℕ} (hk : 2 ≤ k) {m : ℕ} (hm : 2 ≤ m) (hm2 : m + 2 ≤ k)
    {T ν : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    {u₀ : Hm (k + 1)} {u : XTs k T} (hu : IsMildS hk hT ν u₀ u)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    mildSDeriv hk hm2 hν hT u₀ u t =
      ν • lapH m (inclExt (add_two_le_succ hm2) hT u t) -
        NSNsucc hm (inclExt (le_succ_succ (InclNSN.le_of_add_two_le hm2)) hT u t) := by
  rw [mildSDeriv_eq_lap hk hm2 hν hT hu ht,
    incl_nsnExt_eq_NSNsucc hk hm hm2 hT u t]

theorem derivWithin_inclExt_eq_NSNsucc
    {k : ℕ} (hk : 2 ≤ k) {m : ℕ} (hm : 2 ≤ m) (hm2 : m + 2 ≤ k)
    {T ν : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    {u₀ : Hm (k + 1)} {u : XTs k T} (hu : IsMildS hk hT ν u₀ u)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    derivWithin (inclExt (le_succ_of_add_two_le hm2) hT u) (Ico 0 T) t =
      ν • lapH m (inclExt (add_two_le_succ hm2) hT u t) -
        NSNsucc hm (inclExt (le_succ_succ (InclNSN.le_of_add_two_le hm2)) hT u t) := by
  have htIcc : t ∈ Icc (0 : ℝ) T := ⟨ht.1, le_of_lt ht.2⟩
  rw [← mildSDeriv_eq_NSNsucc hk hm hm2 hν hT hu htIcc]
  exact (hasDerivWithinAt_mildS_incl_Ico hk hm2 hν hT hu ht).derivWithin
    (uniqueDiffOn_Ico (0 : ℝ) T t ht)

#print axioms MildPathSmooth.incl_nsnExt_eq_NSNsucc
#print axioms MildPathSmooth.mildSDeriv_eq_NSNsucc
#print axioms MildPathSmooth.derivWithin_inclExt_eq_NSNsucc

end MildPathSmooth
