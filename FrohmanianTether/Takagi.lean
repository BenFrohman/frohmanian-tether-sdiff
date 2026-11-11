/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import Mathlib

/-!
# The Takagi function is continuous and nowhere differentiable

`takagi x = ∑ₙ 2⁻ⁿ · dist(2ⁿ x, ℤ)`. Nowhere differentiability: on the dyadic interval
`[k/2ⁿ, (k+1)/2ⁿ]` containing `x`, `2ⁿ (T((k+1)/2ⁿ) − T(k/2ⁿ))` is an integer of the parity
of `n` (`dyadic_slope`, `parity_sum`), so consecutive slopes differ by at least `1`, while
differentiability would force them to converge (`slope_close`).
Used by `FrohmanianTether.TetherRateCounterexample`.
-/

open Real Filter Topology

noncomputable section
namespace Takagi

def tri (x : ℝ) : ℝ := |x - round x|

lemma continuous_tri : Continuous tri := by
  have : tri = fun x : ℝ => ‖(x : AddCircle (1 : ℝ))‖ := by
    funext x; rw [AddCircle.norm_eq]; simp [tri]
  rw [this]; exact continuous_norm.comp (AddCircle.continuous_mk' 1)

lemma tri_nonneg (x : ℝ) : 0 ≤ tri x := abs_nonneg _
lemma tri_le (x : ℝ) : tri x ≤ 1 / 2 := abs_sub_round x
lemma tri_intCast (k : ℤ) : tri k = 0 := by simp [tri]

lemma tri_div_pow (k : ℤ) (j : ℕ) :
    (2 : ℝ) ^ j * tri ((k : ℝ) / 2 ^ j) =
      ((min (k % 2 ^ j) (2 ^ j - k % 2 ^ j) : ℤ) : ℝ) := by
  have hN : (0 : ℝ) < 2 ^ j := by positivity
  have hf : Int.fract ((k : ℝ) / 2 ^ j) = ((k % (2 ^ j : ℕ) : ℤ) : ℝ) / 2 ^ j := by
    have := Int.fract_div_intCast_eq_div_intCast_mod (k := ℝ) (m := k) (n := 2 ^ j)
    push_cast at this ⊢; exact this
  rw [tri, abs_sub_round_eq_min, hf]
  push_cast
  rw [mul_min_of_nonneg _ _ hN.le]
  congr 1
  · field_simp
  · field_simp


/-- integer jump `e j k`. -/
def ejump (j : ℕ) (k : ℤ) : ℤ :=
  min ((k + 1) % 2 ^ j) (2 ^ j - (k + 1) % 2 ^ j) - min (k % 2 ^ j) (2 ^ j - k % 2 ^ j)

lemma ejump_eq (j : ℕ) (hj : 1 ≤ j) (k : ℤ) : ejump j k = 1 ∨ ejump j k = -1 := by
  obtain ⟨M, hM⟩ : ∃ M : ℤ, (2 : ℤ) ^ j = 2 * M := ⟨2 ^ (j - 1), by
    rw [← pow_succ']; congr 1; omega⟩
  have hNpos : (0 : ℤ) < 2 ^ j := by positivity
  have hr0 : 0 ≤ k % 2 ^ j := Int.emod_nonneg _ hNpos.ne'
  have hr1 : k % 2 ^ j < 2 ^ j := Int.emod_lt_of_pos _ hNpos
  have hr' : (k + 1) % 2 ^ j = (k % 2 ^ j + 1) % 2 ^ j := by
    exact (Int.emod_add_emod k (2 ^ j) 1).symm
  have hcase : (k + 1) % 2 ^ j = k % 2 ^ j + 1 ∨
      ((k + 1) % 2 ^ j = 0 ∧ k % 2 ^ j + 1 = 2 ^ j) := by
    rw [hr']
    rcases lt_or_eq_of_le (show k % 2 ^ j + 1 ≤ 2 ^ j by omega) with h | h
    · left; exact Int.emod_eq_of_lt (by omega) h
    · right; exact ⟨by rw [h, Int.emod_self], h⟩
  unfold ejump
  generalize k % 2 ^ j = r at *
  generalize (k + 1) % 2 ^ j = r' at *
  generalize (2 : ℤ) ^ j = N at *
  subst hM
  rcases hcase with h | ⟨h1, h2⟩ <;> subst_vars <;> omega

lemma ejump_cast_zmod (j : ℕ) (hj : 1 ≤ j) (k : ℤ) : ((ejump j k : ℤ) : ZMod 2) = 1 := by
  rcases ejump_eq j hj k with h | h <;> rw [h] <;> decide

def takagi (x : ℝ) : ℝ := ∑' n : ℕ, (1 / 2 : ℝ) ^ n * tri (2 ^ n * x)

lemma term_le (n : ℕ) (x : ℝ) : ‖(1 / 2 : ℝ) ^ n * tri (2 ^ n * x)‖ ≤ (1 / 2 : ℝ) ^ n := by
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (tri_nonneg _))]
  exact mul_le_of_le_one_right (by positivity) ((tri_le _).trans (by norm_num))

lemma summable_term (x : ℝ) : Summable fun n : ℕ => (1 / 2 : ℝ) ^ n * tri (2 ^ n * x) :=
  Summable.of_norm_bounded (summable_geometric_of_lt_one (by norm_num) (by norm_num))
    (fun n => term_le n x)

lemma continuous_takagi : Continuous takagi :=
  continuous_tsum (fun n => continuous_const.mul (continuous_tri.comp
    (continuous_const.mul continuous_id))) (summable_geometric_of_lt_one (by norm_num) (by norm_num))
    (fun n x => term_le n x)

lemma takagi_nonneg (x : ℝ) : 0 ≤ takagi x :=
  tsum_nonneg fun n => mul_nonneg (by positivity) (tri_nonneg _)

lemma takagi_le_two (x : ℝ) : takagi x ≤ 2 := by
  have h := (summable_term x).tsum_le_tsum (fun n => (Real.le_norm_self _).trans (term_le n x))
    (summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num))
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at h
  unfold takagi; norm_num at h ⊢; linarith

/-- vanishing tail at dyadic points. -/
lemma tri_dyadic_high (k : ℤ) {n m : ℕ} (h : n ≤ m) : tri (2 ^ m * ((k : ℝ) / 2 ^ n)) = 0 := by
  have : (2 : ℝ) ^ m * ((k : ℝ) / 2 ^ n) = ((k * 2 ^ (m - n) : ℤ) : ℝ) := by
    push_cast
    have h2 : (2 : ℝ) ^ m = 2 ^ (m - n) * 2 ^ n := by rw [← pow_add, Nat.sub_add_cancel h]
    rw [h2]
    field_simp
  rw [this, tri_intCast]

lemma tri_dyadic_low (k : ℤ) {n m : ℕ} (h : m ≤ n) :
    2 ^ m * ((k : ℝ) / 2 ^ n) = (k : ℝ) / 2 ^ (n - m) := by
  rw [show n = (n - m) + m by omega, pow_add]
  field_simp
  simp

/-- `2^n (T((k+1)/2^n) - T(k/2^n)) = Σ_{m<n} e(n-m, k)`. -/
lemma dyadic_slope (k : ℤ) (n : ℕ) :
    (2 : ℝ) ^ n * (takagi (((k + 1 : ℤ) : ℝ) / 2 ^ n) - takagi ((k : ℝ) / 2 ^ n)) =
      ((∑ m ∈ Finset.range n, ejump (n - m) k : ℤ) : ℝ) := by
  unfold takagi
  rw [← (summable_term _).tsum_sub (summable_term _)]
  rw [tsum_eq_sum (s := Finset.range n) (fun m hm => by
    simp only [Finset.mem_range, not_lt] at hm
    rw [tri_dyadic_high _ hm, tri_dyadic_high _ hm]; simp)]
  rw [Finset.mul_sum, Int.cast_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m ≤ n := (Finset.mem_range.mp hm).le
  rw [tri_dyadic_low (k + 1) hm', tri_dyadic_low k hm']
  have h1 := tri_div_pow (k + 1) (n - m)
  have h2 := tri_div_pow k (n - m)
  have he : ((ejump (n - m) k : ℤ) : ℝ) =
      2 ^ (n - m) * tri (((k + 1 : ℤ) : ℝ) / 2 ^ (n - m)) -
        2 ^ (n - m) * tri ((k : ℝ) / 2 ^ (n - m)) := by
    rw [h1, h2]; unfold ejump; push_cast; ring
  rw [he]
  generalize tri (((k + 1 : ℤ) : ℝ) / 2 ^ (n - m)) = a
  generalize tri ((k : ℝ) / 2 ^ (n - m)) = b
  have hp : (2 : ℝ) ^ n = 2 ^ (n - m) * 2 ^ m := by rw [← pow_add]; congr 1; omega
  have h3 : (2 : ℝ) ^ m * (1 / 2) ^ m = 1 := by rw [← mul_pow]; norm_num
  rw [hp]
  linear_combination (2 ^ (n - m) * (a - b)) * h3

lemma parity_sum (k : ℤ) (n : ℕ) :
    (((∑ m ∈ Finset.range n, ejump (n - m) k : ℤ)) : ZMod 2) = n := by
  push_cast
  rw [Finset.sum_congr rfl (g := fun _ => (1 : ZMod 2)) (fun m hm => ejump_cast_zmod _
    (by have := Finset.mem_range.mp hm; omega) k)]
  simp


lemma slope_close {x L : ℝ} (hL : HasDerivAt takagi L x) :
    ∃ N : ℕ, ∀ n ≥ N, |((∑ m ∈ Finset.range n, ejump (n - m) ⌊2 ^ n * x⌋ : ℤ) : ℝ) - L| ≤ 1 / 4 := by
  have ho := hL.isLittleO
  have hev := ho.def (show (0 : ℝ) < 1 / 4 by norm_num)
  obtain ⟨dd, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨N, fun n hn => ?_⟩
  set k := ⌊2 ^ n * x⌋ with hk
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  set a : ℝ := (k : ℝ) / 2 ^ n
  set b : ℝ := ((k + 1 : ℤ) : ℝ) / 2 ^ n
  have hax : a ≤ x := by
    simp only [a]; rw [div_le_iff₀ hpos, mul_comm]; exact Int.floor_le _
  have hxb : x < b := by
    simp only [b]; rw [lt_div_iff₀ hpos, mul_comm]; push_cast; exact Int.lt_floor_add_one _
  have hba : b - a = (1 / 2) ^ n := by
    simp only [a, b]; push_cast; rw [one_div_pow]; field_simp; ring
  have hsmall : (1 / 2 : ℝ) ^ n < dd :=
    lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn) hN
  have hb := hball (y := b) (by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith)
  have ha := hball (y := a) (by rw [Real.dist_eq, abs_of_nonpos (by linarith)]; linarith)
  simp only [Real.norm_eq_abs, smul_eq_mul] at ha hb
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - x)] at hb
  rw [abs_of_nonpos (by linarith : a - x ≤ 0)] at ha
  have hD := dyadic_slope k n
  rw [← hD]
  have h1 : |takagi b - takagi a - (b - a) * L| ≤ 1 / 4 * (b - a) := by
    have := abs_sub (takagi b - takagi x - (b - x) * L) (takagi a - takagi x - (a - x) * L)
    have e : takagi b - takagi x - (b - x) * L - (takagi a - takagi x - (a - x) * L) =
        takagi b - takagi a - (b - a) * L := by ring
    rw [e] at this
    linarith
  have e2 : (2 : ℝ) ^ n * (takagi b - takagi a) - L =
      2 ^ n * (takagi b - takagi a - (b - a) * L) := by
    have h3 : (2 : ℝ) ^ n * (1 / 2) ^ n = 1 := by rw [← mul_pow]; norm_num
    rw [hba]; linear_combination L * h3
  rw [e2, abs_mul, abs_of_pos hpos]
  calc 2 ^ n * |takagi b - takagi a - (b - a) * L| ≤ 2 ^ n * (1 / 4 * (b - a)) :=
        mul_le_mul_of_nonneg_left h1 hpos.le
    _ = 1 / 4 := by rw [hba, ← mul_assoc, mul_comm _ (1 / 4 : ℝ), mul_assoc, ← mul_pow]; norm_num

/-- **The Takagi function is nowhere differentiable.** -/
theorem not_differentiableAt_takagi (x : ℝ) : ¬ DifferentiableAt ℝ takagi x := by
  intro hd
  obtain ⟨N, hN⟩ := slope_close hd.hasDerivAt
  set I0 : ℤ := ∑ m ∈ Finset.range N, ejump (N - m) ⌊2 ^ N * x⌋
  set I1 : ℤ := ∑ m ∈ Finset.range (N + 1), ejump (N + 1 - m) ⌊2 ^ (N + 1) * x⌋
  have h0 := hN N le_rfl
  have h1 := hN (N + 1) (Nat.le_succ N)
  have hne : I1 ≠ I0 := by
    intro h
    have c0 := parity_sum ⌊2 ^ N * x⌋ N
    have c1 := parity_sum ⌊2 ^ (N + 1) * x⌋ (N + 1)
    have : ((N + 1 : ℕ) : ZMod 2) = (N : ZMod 2) := by
      rw [← c1, ← c0]; exact congrArg _ h
    push_cast at this
    simp at this
  have hI : (1 : ℝ) ≤ |(I1 : ℝ) - I0| := by
    have : (1 : ℤ) ≤ |I1 - I0| := Int.one_le_abs (sub_ne_zero.mpr hne)
    exact_mod_cast this
  have := abs_sub_le (I1 : ℝ) (deriv takagi x) I0
  rw [abs_sub_comm (deriv takagi x)] at this
  linarith

end Takagi

end

#print axioms Takagi.not_differentiableAt_takagi
#print axioms Takagi.continuous_takagi
