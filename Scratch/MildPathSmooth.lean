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

lemma le_succ_of_mul_two_le {m n k : ℕ} (hn : m + 2 * n ≤ k) : m ≤ k + 1 :=
  ((Nat.le_add_right m (2 * n)).trans hn).trans (Nat.le_succ k)

lemma add_two_le_of_mul_succ {m n k : ℕ} (hn : m + 2 * (n + 1) ≤ k) : m + 2 ≤ k := by
  have h : m + 2 ≤ m + 2 * (n + 1) := by
    have : 2 ≤ 2 * (n + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos n)
    exact Nat.add_le_add_left this m
  exact h.trans hn

lemma add_two_mul_le_of_succ {m n k : ℕ} (hn : m + 2 * (n + 1) ≤ k) :
    m + 2 + 2 * n ≤ k := by
  convert hn using 1
  ring

lemma add_one_mul_le_of_succ {m n k : ℕ} (hn : m + 2 * (n + 1) ≤ k) :
    m + 1 + 2 * n ≤ k := by
  have h := add_two_mul_le_of_succ hn
  omega

/-- The Laplacian `Ĥ^{m+2} → Ĥ^m` is `C^∞` as a real map. -/
theorem contDiff_lapH (m : ℕ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun G : Hm (m + 2) => (lapH m) G) :=
  (isBoundedLinearMap_restrictCLM (lapH m)
    (fun c x => real_smul_eq_coe_smul c x)
    (fun c y => real_smul_eq_coe_smul c y)).contDiff

/-- If `m ≥ 2` and `m + 2n ≤ k`, the included mild path is `C^n` in `Ĥ^m`
on `[0, T)`. -/
theorem contDiffOn_inclExt
    {k : ℕ} (hk : 2 ≤ k) {m : ℕ} (hm : 2 ≤ m) {n : ℕ} (hn : m + 2 * n ≤ k)
    {T ν : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    {u₀ : Hm (k + 1)} {u : XTs k T} (hu : IsMildS hk hT ν u₀ u) :
    ContDiffOn ℝ n (inclExt (le_succ_of_mul_two_le hn) hT u) (Ico 0 T) := by
  induction n generalizing m with
  | zero =>
    exact contDiffOn_zero.2
      (continuous_inclExt (le_succ_of_mul_two_le hn) hT u).continuousOn
  | succ n ih =>
    by_cases hTpos : 0 < T
    · have hm2 : m + 2 ≤ k := add_two_le_of_mul_succ hn
      have hn2 : m + 2 + 2 * n ≤ k := add_two_mul_le_of_succ hn
      have hn1 : m + 1 + 2 * n ≤ k := add_one_mul_le_of_succ hn
      have hfun :
          inclExt (le_succ_of_mul_two_le hn) hT u =
            inclExt (le_succ_of_add_two_le hm2) hT u :=
        inclExt_irrel _ _ hT u
      rw [hfun, show ((n.succ : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1
        from Nat.cast_succ n]
      rw [contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ico (0 : ℝ) T)]
      refine ⟨?diff, ?analytic, ?der⟩
      · intro t0 ht0
        exact (hasDerivWithinAt_mildS_incl_Ico hk hm2 hν hT hu ht0).differentiableWithinAt
      · intro hω
        exact (WithTop.natCast_ne_top n hω).elim
      · have hder : ∀ t0 ∈ Ico (0 : ℝ) T,
            derivWithin (inclExt (le_succ_of_add_two_le hm2) hT u) (Ico 0 T) t0 =
              ν • lapH m (inclExt (add_two_le_succ hm2) hT u t0) -
                NSNsucc hm (inclExt (le_succ_succ (InclNSN.le_of_add_two_le hm2))
                  hT u t0) :=
          fun t0 ht0 => derivWithin_inclExt_eq_NSNsucc hk hm hm2 hν hT hu ht0
        have hih2 := ih (m := m + 2) (Nat.le_add_left 2 m) hn2
        have hfun2 :
            inclExt (le_succ_of_mul_two_le hn2) hT u =
              inclExt (add_two_le_succ hm2) hT u :=
          inclExt_irrel _ _ hT u
        rw [hfun2] at hih2
        have hih1 := ih (m := m + 1) (Nat.le_succ_of_le hm) hn1
        have hfun1 :
            inclExt (le_succ_of_mul_two_le hn1) hT u =
              inclExt (le_succ_succ (InclNSN.le_of_add_two_le hm2)) hT u :=
          inclExt_irrel _ _ hT u
        rw [hfun1] at hih1
        have hlap0 : ContDiffOn ℝ n
            (fun t => lapH m (inclExt (add_two_le_succ hm2) hT u t))
            (Ico 0 T) :=
          (contDiff_lapH m).comp_contDiffOn hih2
        have hlap : ContDiffOn ℝ n
            (fun t => ν • lapH m (inclExt (add_two_le_succ hm2) hT u t))
            (Ico 0 T) :=
          ContDiffOn.const_smul ν hlap0
        have hN : ContDiffOn ℝ n
            (fun t => NSNsucc hm
              (inclExt (le_succ_succ (InclNSN.le_of_add_two_le hm2)) hT u t))
            (Ico 0 T) :=
          (contDiff_NSNsucc hm).comp_contDiffOn hih1
        exact (hlap.sub hN).congr hder
    · have hempty : Ico (0 : ℝ) T = ∅ :=
        Ico_eq_empty_iff.2 (not_lt.2 (le_of_not_gt hTpos))
      rw [hempty]
      exact contDiffOn_empty

/-- For `m ≤ 2`, include a `C^n` path from level `2`. -/
theorem contDiffOn_inclExt_of_le_two
    {k : ℕ} (hk : 2 ≤ k) {m : ℕ} (hm : m ≤ 2) {n : ℕ} (hn : 2 + 2 * n ≤ k)
    {T ν : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    {u₀ : Hm (k + 1)} {u : XTs k T} (hu : IsMildS hk hT ν u₀ u) :
    ContDiffOn ℝ n (inclExt (hm.trans (Nat.le_succ_of_le hk)) hT u)
      (Ico 0 T) := by
  have h2 := contDiffOn_inclExt hk (by norm_num : 2 ≤ 2) hn hν hT hu
  have hcomp :
      inclExt (hm.trans (Nat.le_succ_of_le hk)) hT u =
        fun t => incl hm (inclExt (le_succ_of_mul_two_le hn) hT u t) := by
    funext t
    unfold inclExt
    exact (incl_comp (le_succ_of_mul_two_le hn) hm
      (ContinuousMap.IccExtend hT u t)).symm
  rw [hcomp]
  exact (isBoundedLinearMap_restrictCLM (incl hm)
      (fun c x => real_smul_eq_coe_smul c x)
      (fun c y => real_smul_eq_coe_smul c y)).contDiff.comp_contDiffOn h2

#print axioms MildPathSmooth.contDiff_lapH
#print axioms MildPathSmooth.contDiffOn_inclExt
#print axioms MildPathSmooth.contDiffOn_inclExt_of_le_two

end MildPathSmooth
