import Mathlib
import FrohmanianTether.SymplecticTether

open Real Filter Topology

noncomputable section
namespace TakagiScratch

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

end TakagiScratch


end

open Real

noncomputable section
namespace OneD

def bb (s : ℝ) : ℝ := (1 + s ^ 2)⁻¹
def bb1 (s : ℝ) : ℝ := -2 * s * ((1 + s ^ 2) ^ 2)⁻¹
def bb2 (s : ℝ) : ℝ := (6 * s ^ 2 - 2) * ((1 + s ^ 2) ^ 3)⁻¹

lemma pos1 (s : ℝ) : 0 < 1 + s ^ 2 := by positivity

lemma hq (s : ℝ) : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * s) s := by
  simpa using (hasDerivAt_pow 2 s).const_add 1

lemma hw (k : ℕ) (s : ℝ) : HasDerivAt (fun x : ℝ => ((1 + x ^ 2) ^ k)⁻¹)
    (-(k * (1 + s ^ 2) ^ (k - 1) * (2 * s)) / ((1 + s ^ 2) ^ k) ^ 2) s := by
  have h := ((hq s).pow k).inv (pow_ne_zero _ (pos1 s).ne')
  simpa using h

lemma hasDerivAt_bb (s : ℝ) : HasDerivAt bb (bb1 s) s := by
  have h := (hw 1 s)
  simp only [pow_one] at h
  convert h using 1
  simp [bb1]; field_simp

lemma hasDerivAt_bb1 (s : ℝ) : HasDerivAt bb1 (bb2 s) s := by
  have h := ((hasDerivAt_id s).const_mul (-2)).mul (hw 2 s)
  convert h using 1
  simp [bb2]; field_simp; ring

/-- `a(s) = sin(s⁵) / (1+s²)³`. -/
def aa (s : ℝ) : ℝ := Real.sin (s ^ 5) * ((1 + s ^ 2) ^ 3)⁻¹
def aa1 (s : ℝ) : ℝ :=
  5 * s ^ 4 * Real.cos (s ^ 5) * ((1 + s ^ 2) ^ 3)⁻¹ -
    6 * s * Real.sin (s ^ 5) * ((1 + s ^ 2) ^ 4)⁻¹
def aa2 (s : ℝ) : ℝ :=
  (20 * s ^ 3 * Real.cos (s ^ 5) - 25 * s ^ 8 * Real.sin (s ^ 5)) * ((1 + s ^ 2) ^ 3)⁻¹ -
    (30 * s ^ 5 * Real.cos (s ^ 5) + 30 * s ^ 5 * Real.cos (s ^ 5)) * ((1 + s ^ 2) ^ 4)⁻¹ +
    Real.sin (s ^ 5) * (-6 * ((1 + s ^ 2) ^ 4)⁻¹ + 48 * s ^ 2 * ((1 + s ^ 2) ^ 5)⁻¹)

lemma hasDerivAt_aa (s : ℝ) : HasDerivAt aa (aa1 s) s := by
  have hs := (Real.hasDerivAt_sin (s ^ 5)).comp s (hasDerivAt_pow 5 s)
  convert hs.mul (hw 3 s) using 1
  simp [aa1]; field_simp; ring

lemma hasDerivAt_aa1 (s : ℝ) : HasDerivAt aa1 (aa2 s) s := by
  have p5 := hasDerivAt_pow 5 s
  have hc := (Real.hasDerivAt_cos (s ^ 5)).comp s p5
  have hs := (Real.hasDerivAt_sin (s ^ 5)).comp s p5
  have h := ((((hasDerivAt_pow 4 s).const_mul 5).mul hc).mul (hw 3 s)).sub
    ((((hasDerivAt_id s).const_mul 6).mul hs).mul (hw 4 s))
  convert h using 1
  simp [aa2]; field_simp; ring


lemma bb_pos (s : ℝ) : 0 < bb s := inv_pos.mpr (pos1 s)
lemma bb_le_one (s : ℝ) : bb s ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg s])
lemma bb_zero : bb 0 = 1 := by simp [bb]
lemma bb2_zero : bb2 0 = -2 := by simp [bb2]

lemma winv_le (s : ℝ) {k : ℕ} (hk : 1 ≤ k) : ((1 + s ^ 2) ^ k)⁻¹ ≤ bb s := by
  unfold bb
  exact inv_anti₀ (pos1 s) (le_self_pow₀ (by nlinarith [sq_nonneg s]) (by omega))

lemma abs_aa_le (s : ℝ) : |aa s| ≤ bb s := by
  unfold aa
  rw [abs_mul, abs_of_pos (inv_pos.mpr (pow_pos (pos1 s) 3))]
  calc |Real.sin (s ^ 5)| * ((1 + s ^ 2) ^ 3)⁻¹ ≤ 1 * ((1 + s ^ 2) ^ 3)⁻¹ :=
        mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)
    _ ≤ bb s := by rw [one_mul]; exact winv_le s (by norm_num)

lemma abs_bb1_le (s : ℝ) : |bb1 s| ≤ bb s := by
  unfold bb1 bb
  have hp := pos1 s
  rw [abs_mul, abs_of_pos (inv_pos.mpr (pow_pos hp 2)), abs_mul]
  rw [show |(-2 : ℝ)| = 2 by norm_num]
  have h2 : 2 * |s| ≤ 1 + s ^ 2 := by
    nlinarith [sq_nonneg (|s| - 1), sq_abs s]
  rw [show ((1 + s ^ 2) ^ 2)⁻¹ = (1 + s ^ 2)⁻¹ * (1 + s ^ 2)⁻¹ by rw [sq, mul_inv]]
  have hi : 0 < (1 + s ^ 2)⁻¹ := inv_pos.mpr hp
  calc 2 * |s| * ((1 + s ^ 2)⁻¹ * (1 + s ^ 2)⁻¹) = (2 * |s| * (1 + s ^ 2)⁻¹) * (1 + s ^ 2)⁻¹ := by ring
    _ ≤ 1 * (1 + s ^ 2)⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ hi.le
        rw [← div_eq_mul_inv, div_le_one hp]; exact h2
    _ = (1 + s ^ 2)⁻¹ := one_mul _

lemma s4_le (s : ℝ) : s ^ 4 * ((1 + s ^ 2) ^ 3)⁻¹ ≤ bb s := by
  unfold bb
  have hp := pos1 s
  rw [← div_eq_mul_inv, div_le_iff₀ (pow_pos hp 3)]
  rw [show (1 + s ^ 2) ^ 3 = (1 + s ^ 2) * (1 + s ^ 2) ^ 2 by ring, ← mul_assoc,
    inv_mul_cancel₀ hp.ne', one_mul]
  nlinarith [sq_nonneg s, sq_nonneg (s ^ 2)]

lemma s1_le (s : ℝ) : |s| * ((1 + s ^ 2) ^ 4)⁻¹ ≤ bb s := by
  unfold bb
  have hp := pos1 s
  rw [← div_eq_mul_inv, div_le_iff₀ (pow_pos hp 4)]
  rw [show (1 + s ^ 2) ^ 4 = (1 + s ^ 2) * (1 + s ^ 2) ^ 3 by ring, ← mul_assoc,
    inv_mul_cancel₀ hp.ne', one_mul]
  have h1 : |s| ≤ 1 + s ^ 2 := by nlinarith [sq_nonneg (|s| - 1), sq_abs s]
  have h2 : 1 + s ^ 2 ≤ (1 + s ^ 2) ^ 3 := le_self_pow₀ (by nlinarith [sq_nonneg s]) (by norm_num)
  linarith

lemma abs_aa1_le (s : ℝ) : |aa1 s| ≤ 11 * bb s := by
  unfold aa1
  have hp := pos1 s
  have e1 : |5 * s ^ 4 * Real.cos (s ^ 5) * ((1 + s ^ 2) ^ 3)⁻¹| ≤ 5 * bb s := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr (pow_pos hp 3)),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ s ^ 4)]
    have := s4_le s
    have hc := Real.abs_cos_le_one (s ^ 5)
    have : 0 ≤ s ^ 4 * ((1 + s ^ 2) ^ 3)⁻¹ := by positivity
    calc |(5 : ℝ)| * s ^ 4 * |Real.cos (s ^ 5)| * ((1 + s ^ 2) ^ 3)⁻¹
        = 5 * (s ^ 4 * ((1 + s ^ 2) ^ 3)⁻¹) * |Real.cos (s ^ 5)| := by norm_num; ring
      _ ≤ 5 * (s ^ 4 * ((1 + s ^ 2) ^ 3)⁻¹) * 1 := by gcongr
      _ ≤ 5 * bb s := by linarith
  have e2 : |6 * s * Real.sin (s ^ 5) * ((1 + s ^ 2) ^ 4)⁻¹| ≤ 6 * bb s := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr (pow_pos hp 4))]
    have := s1_le s
    have hc := Real.abs_sin_le_one (s ^ 5)
    have : 0 ≤ |s| * ((1 + s ^ 2) ^ 4)⁻¹ := by positivity
    calc |(6 : ℝ)| * |s| * |Real.sin (s ^ 5)| * ((1 + s ^ 2) ^ 4)⁻¹
        = 6 * (|s| * ((1 + s ^ 2) ^ 4)⁻¹) * |Real.sin (s ^ 5)| := by norm_num; ring
      _ ≤ 6 * (|s| * ((1 + s ^ 2) ^ 4)⁻¹) * 1 := by gcongr
      _ ≤ 6 * bb s := by linarith
  calc _ ≤ _ := abs_sub _ _
    _ ≤ 5 * bb s + 6 * bb s := add_le_add e1 e2
    _ = 11 * bb s := by ring

/-- At `s⁵ = π/2 + 2πn`: `aa2 s - 2 aa s` has modulus `≥ 25 s²/8 - 56` for `s ≥ 1`. -/
lemma aa2_large {s : ℝ} (hs : 1 ≤ s) (hsin : Real.sin (s ^ 5) = 1) (hcos : Real.cos (s ^ 5) = 0) :
    25 * s ^ 2 / 8 - 56 ≤ |aa2 s - 2 * aa s| := by
  have hp := pos1 s
  have e : aa2 s - 2 * aa s = -(25 * (s ^ 8 * ((1 + s ^ 2) ^ 3)⁻¹)) +
      (-6 * ((1 + s ^ 2) ^ 4)⁻¹ + 48 * (s ^ 2 * ((1 + s ^ 2) ^ 5)⁻¹) - 2 * ((1 + s ^ 2) ^ 3)⁻¹) := by
    simp only [aa2, aa, hsin, hcos]; ring
  have w3 : ((1 + s ^ 2) ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by nlinarith))
  have w4 : 0 ≤ ((1 + s ^ 2) ^ 4)⁻¹ := by positivity
  have w4' : ((1 + s ^ 2) ^ 4)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by nlinarith))
  have w5 : s ^ 2 * ((1 + s ^ 2) ^ 5)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one (pow_pos hp 5)]
    nlinarith [le_self_pow₀ (show 1 ≤ 1 + s ^ 2 by nlinarith) (show 5 ≠ 0 by norm_num)]
  have w5' : 0 ≤ s ^ 2 * ((1 + s ^ 2) ^ 5)⁻¹ := by positivity
  have w3' : 0 ≤ ((1 + s ^ 2) ^ 3)⁻¹ := by positivity
  have big : 25 * s ^ 2 / 8 ≤ 25 * (s ^ 8 * ((1 + s ^ 2) ^ 3)⁻¹) := by
    rw [← div_eq_mul_inv, mul_div_assoc']
    rw [div_le_div_iff₀ (by norm_num) (pow_pos hp 3)]
    have h1 : 1 + s ^ 2 ≤ 2 * s ^ 2 := by nlinarith
    have h2 : (1 + s ^ 2) ^ 3 ≤ (2 * s ^ 2) ^ 3 := pow_le_pow_left₀ hp.le h1 3
    nlinarith [pow_pos (show 0 < s by linarith) 2]
  rw [e]
  have : -(25 * (s ^ 8 * ((1 + s ^ 2) ^ 3)⁻¹)) +
      (-6 * ((1 + s ^ 2) ^ 4)⁻¹ + 48 * (s ^ 2 * ((1 + s ^ 2) ^ 5)⁻¹) - 2 * ((1 + s ^ 2) ^ 3)⁻¹)
      ≤ -(25 * s ^ 2 / 8) + 48 := by nlinarith
  exact le_trans (by linarith) (neg_le_abs _)

/-- `aa2 - 2 aa` is unbounded. -/
lemma aa2_unbounded (K : ℝ) : ∃ s : ℝ, K < |aa2 s - 2 * aa s| := by
  set R : ℝ := |K| + 60
  have hR : 1 ≤ R := by have := abs_nonneg K; simp only [R]; linarith
  obtain ⟨n, hn⟩ := exists_nat_ge (R ^ 5)
  set X : ℝ := Real.pi / 2 + n * (2 * Real.pi)
  have hX : 0 ≤ X := by positivity
  set s : ℝ := X ^ ((5 : ℕ)⁻¹ : ℝ)
  have hs5 : s ^ 5 = X := Real.rpow_inv_natCast_pow hX (by norm_num)
  have hs0 : 0 ≤ s := Real.rpow_nonneg hX _
  have hXn : (n : ℝ) ≤ X := by
    have := Real.pi_gt_three
    simp only [X]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hRs : R ≤ s := by
    have : R ^ 5 ≤ s ^ 5 := by rw [hs5]; linarith
    exact (pow_le_pow_iff_left₀ (by linarith) hs0 (by norm_num)).mp this
  have hsin : Real.sin (s ^ 5) = 1 := by rw [hs5, Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two]
  have hcos : Real.cos (s ^ 5) = 0 := by rw [hs5, Real.cos_add_nat_mul_two_pi, Real.cos_pi_div_two]
  refine ⟨s, ?_⟩
  have h := aa2_large (by linarith) hsin hcos
  have : R ≤ s ^ 2 := by nlinarith
  have := le_abs_self K
  simp only [R] at *
  nlinarith

end OneD

end
noncomputable section

namespace TetherRateCounterexample

open NavierStokes3D FrohmanianTether TakagiScratch OneD MeasureTheory

/-- directional derivative along a line. -/
lemma fderiv_line {f : T3 → ℝ} {x v : T3} {d : ℝ} (hf : DifferentiableAt ℝ f x)
    (hd : HasDerivAt (fun s : ℝ => f (x + s • v)) d 0) : fderiv ℝ f x v = d := by
  have hl : HasDerivAt (fun s : ℝ => x + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have h2 := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  exact h2.unique hd

lemma shift {g : ℝ → ℝ} {g' a : ℝ} (h : HasDerivAt g g' a) :
    HasDerivAt (fun s => g (a + s)) g' 0 := by
  have h' : HasDerivAt g g' (0 + a) := by simpa using h
  simpa [add_comm] using h'.comp_add_const 0 a

def c0 (y : T3) : ℝ := aa (y 0) * bb1 (y 1) * bb (y 2)
def c1 (y : T3) : ℝ := -(aa1 (y 0) * bb (y 1) * bb (y 2))
def c2 (y : T3) : ℝ := takagi (y 2) * (bb (y 0) * bb (y 1) * bb (y 2))

/-- The counterexample field: smooth first two components (a stream-function pair),
nowhere-differentiable third component. -/
def U : VelocityField := fun y => WithLp.toLp 2 ![c0 y, c1 y, c2 y]

lemma U0 : (fun y => U y 0) = c0 := rfl
lemma U1 : (fun y => U y 1) = c1 := rfl
lemma U2 : (fun y => U y 2) = c2 := rfl

lemma diff_aa : Differentiable ℝ aa := fun s => (hasDerivAt_aa s).differentiableAt
lemma diff_aa1 : Differentiable ℝ aa1 := fun s => (hasDerivAt_aa1 s).differentiableAt
lemma diff_bb : Differentiable ℝ bb := fun s => (hasDerivAt_bb s).differentiableAt
lemma diff_bb1 : Differentiable ℝ bb1 := fun s => (hasDerivAt_bb1 s).differentiableAt

lemma dcoord (j : Fin 3) : Differentiable ℝ (fun y : T3 => y j) :=
  (EuclideanSpace.proj j : T3 →L[ℝ] ℝ).differentiable

lemma diff_c0 : Differentiable ℝ c0 :=
  ((diff_aa.comp (dcoord 0)).mul (diff_bb1.comp (dcoord 1))).mul (diff_bb.comp (dcoord 2))
lemma diff_c1 : Differentiable ℝ c1 :=
  (((diff_aa1.comp (dcoord 0)).mul (diff_bb.comp (dcoord 1))).mul (diff_bb.comp (dcoord 2))).neg

lemma line0 (x : T3) (s : ℝ) : (x + s • EuclideanSpace.single 0 (1 : ℝ)) =
    WithLp.toLp 2 ![x 0 + s, x 1, x 2] := by
  ext j; fin_cases j <;> simp
lemma line1 (x : T3) (s : ℝ) : (x + s • EuclideanSpace.single 1 (1 : ℝ)) =
    WithLp.toLp 2 ![x 0, x 1 + s, x 2] := by
  ext j; fin_cases j <;> simp
lemma line2 (x : T3) (s : ℝ) : (x + s • EuclideanSpace.single 2 (1 : ℝ)) =
    WithLp.toLp 2 ![x 0, x 1, x 2 + s] := by
  ext j; fin_cases j <;> simp

lemma d0c0 (x : T3) : fderiv ℝ c0 x (EuclideanSpace.single 0 1) =
    aa1 (x 0) * bb1 (x 1) * bb (x 2) := by
  apply fderiv_line (diff_c0 x)
  simp only [line0, c0]
  simpa using ((shift (hasDerivAt_aa (x 0))).mul_const (bb1 (x 1))).mul_const (bb (x 2))

lemma d1c0 (x : T3) : fderiv ℝ c0 x (EuclideanSpace.single 1 1) =
    aa (x 0) * bb2 (x 1) * bb (x 2) := by
  apply fderiv_line (diff_c0 x)
  simp only [line1, c0]
  simpa using ((shift (hasDerivAt_bb1 (x 1))).const_mul (aa (x 0))).mul_const (bb (x 2))

lemma d0c1 (x : T3) : fderiv ℝ c1 x (EuclideanSpace.single 0 1) =
    -(aa2 (x 0) * bb (x 1) * bb (x 2)) := by
  apply fderiv_line (diff_c1 x)
  simp only [line0, c1]
  simpa using (((shift (hasDerivAt_aa1 (x 0))).mul_const (bb (x 1))).mul_const (bb (x 2))).neg

lemma d1c1 (x : T3) : fderiv ℝ c1 x (EuclideanSpace.single 1 1) =
    -(aa1 (x 0) * bb1 (x 1) * bb (x 2)) := by
  apply fderiv_line (diff_c1 x)
  simp only [line1, c1]
  simpa using (((shift (hasDerivAt_bb (x 1))).const_mul (aa1 (x 0))).mul_const (bb (x 2))).neg

/-- The third component is nowhere differentiable. -/
lemma not_diff_c2 (y : T3) : ¬ DifferentiableAt ℝ c2 y := by
  intro hd
  have hl : HasDerivAt (fun s : ℝ => y + s • EuclideanSpace.single 2 (1 : ℝ))
      (EuclideanSpace.single 2 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single 2 (1 : ℝ))).const_add y
  have hg : DifferentiableAt ℝ (fun s : ℝ => c2 (y + s • EuclideanSpace.single 2 (1 : ℝ))) 0 :=
    (hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)).differentiableAt
  have hG : DifferentiableAt ℝ (fun s : ℝ => bb (y 0) * bb (y 1) * bb (y 2 + s)) 0 :=
    (differentiableAt_const _).mul ((diff_bb _).comp _ ((differentiableAt_const _).add differentiableAt_id))
  have hq : DifferentiableAt ℝ (fun s : ℝ => c2 (y + s • EuclideanSpace.single 2 (1 : ℝ)) /
      (bb (y 0) * bb (y 1) * bb (y 2 + s))) 0 := hg.div hG (by have := bb_pos (y 0); have := bb_pos (y 1); have := bb_pos (y 2 + 0); positivity)
  have heq : (fun s : ℝ => c2 (y + s • EuclideanSpace.single 2 (1 : ℝ)) /
      (bb (y 0) * bb (y 1) * bb (y 2 + s))) = fun s => takagi (y 2 + s) := by
    funext s
    simp only [line2, c2]
    simp only [Matrix.cons_val]
    have := bb_pos (y 0); have := bb_pos (y 1); have := bb_pos (y 2 + s)
    field_simp
  rw [heq] at hq
  have : DifferentiableAt ℝ (fun t => (fun s => takagi (y 2 + s)) (t - y 2)) (y 2) :=
    DifferentiableAt.comp (y 2) (by rw [sub_self]; exact hq) (differentiableAt_id.sub_const _)
  exact not_differentiableAt_takagi (y 2) (by simpa using this)


lemma not_diff_U (y : T3) : ¬ DifferentiableAt ℝ U y := fun h =>
  not_diff_c2 y (((EuclideanSpace.proj 2 : T3 →L[ℝ] ℝ).differentiableAt).comp y h)

lemma fderiv_U (y : T3) : fderiv ℝ U y = 0 := fderiv_zero_of_not_differentiableAt (not_diff_U y)

lemma convective_U (x : T3) : convective U U x = 0 := by
  simp [convective, fderiv_U]

lemma laplacian_U (x : T3) : laplacian U x = 0 := by
  simp [laplacian, fderiv_U]

lemma div_U (x : T3) : div U x = 0 := by
  unfold div
  rw [Fin.sum_univ_three, U0, U1, U2, d0c0, d1c1,
    fderiv_zero_of_not_differentiableAt (not_diff_c2 x)]
  simp

lemma ns_U (ν : ℝ) : NS_PDE (fun _ => U) (fun _ => fun _ => (0 : ℝ)) ν := by
  intro t _ x
  refine ⟨?_, div_U x⟩
  simp [time_deriv, convective_U, laplacian_U, pressureGradient]

lemma continuous_c2 : Continuous c2 := by
  have hc : ∀ j : Fin 3, Continuous (fun y : T3 => y j) := fun j => (dcoord j).continuous
  exact (continuous_takagi.comp (hc 2)).mul (((diff_bb.continuous.comp (hc 0)).mul
    (diff_bb.continuous.comp (hc 1))).mul (diff_bb.continuous.comp (hc 2)))

lemma continuous_U : Continuous U := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  fin_cases i
  · exact diff_c0.continuous
  · exact diff_c1.continuous
  · exact continuous_c2

/-- `P y = bb y₀ · bb y₁ · bb y₂ ≤ (1 + ‖y‖²)⁻¹`. -/
lemma P_le (y : T3) : bb (y 0) * bb (y 1) * bb (y 2) ≤ (1 + ‖y‖ ^ 2)⁻¹ := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  unfold bb
  rw [← mul_inv, ← mul_inv]
  apply inv_anti₀ (by positivity)
  nlinarith [sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg (y 2),
    mul_nonneg (sq_nonneg (y 0)) (sq_nonneg (y 1)), mul_nonneg (sq_nonneg (y 0)) (sq_nonneg (y 2)),
    mul_nonneg (sq_nonneg (y 1)) (sq_nonneg (y 2)),
    mul_nonneg (mul_nonneg (sq_nonneg (y 0)) (sq_nonneg (y 1))) (sq_nonneg (y 2))]

lemma normU_sq_le (y : T3) : ‖U y‖ ^ 2 ≤ 126 * ((1 : ℝ) + ‖y‖ ^ 2) ^ (-(4 : ℝ) / 2) := by
  set P := bb (y 0) * bb (y 1) * bb (y 2)
  have hP0 : 0 ≤ P := by have := bb_pos (y 0); have := bb_pos (y 1); have := bb_pos (y 2); positivity
  have h0 : |c0 y| ≤ P := by
    unfold c0; rw [abs_mul, abs_mul, abs_of_pos (bb_pos (y 2))]
    have := abs_aa_le (y 0); have := abs_bb1_le (y 1)
    have := bb_pos (y 0); have := bb_pos (y 1); have := bb_pos (y 2)
    simp only [P]; gcongr
  have h1 : |c1 y| ≤ 11 * P := by
    unfold c1; rw [abs_neg, abs_mul, abs_mul, abs_of_pos (bb_pos (y 1)), abs_of_pos (bb_pos (y 2))]
    have := abs_aa1_le (y 0); have := bb_pos (y 1); have := bb_pos (y 2)
    simp only [P]
    calc |aa1 (y 0)| * bb (y 1) * bb (y 2) ≤ (11 * bb (y 0)) * bb (y 1) * bb (y 2) := by gcongr
      _ = 11 * (bb (y 0) * bb (y 1) * bb (y 2)) := by ring
  have h2 : |c2 y| ≤ 2 * P := by
    unfold c2; rw [abs_mul, abs_of_nonneg (takagi_nonneg _), abs_of_nonneg hP0]
    exact mul_le_mul_of_nonneg_right (takagi_le_two _) hP0
  have hn : ‖U y‖ ^ 2 = c0 y ^ 2 + c1 y ^ 2 + c2 y ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]; rfl
  have hPle := P_le y
  have hrp : ((1 : ℝ) + ‖y‖ ^ 2) ^ (-(4 : ℝ) / 2) = ((1 + ‖y‖ ^ 2)⁻¹) ^ 2 := by
    rw [show -(4 : ℝ) / 2 = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity),
      Real.rpow_natCast, inv_pow]
  rw [hn, hrp]
  have e0 : c0 y ^ 2 ≤ P ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h0 2
  have e1 : c1 y ^ 2 ≤ (11 * P) ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have e2 : c2 y ^ 2 ≤ (2 * P) ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have e3 : P ^ 2 ≤ ((1 + ‖y‖ ^ 2)⁻¹) ^ 2 := pow_le_pow_left₀ hP0 hPle 2
  nlinarith

lemma integrable_U : Integrable (fun x : T3 => ‖U x‖ ^ 2) := by
  have hg : Integrable (fun x : T3 => ((1 : ℝ) + ‖x‖ ^ 2) ^ (-(4 : ℝ) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (by rw [finrank_euclideanSpace_fin]; norm_num)
  refine (hg.const_mul 126).mono' ((continuous_U.norm.pow 2).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [Real.norm_of_nonneg (by positivity)]
  exact normU_sq_le x

lemma phys_U : IsPhysicalNSSolution (fun _ : ℝ => U) :=
  ⟨fun _ _ _ => differentiableAt_const _, fun _ _ => continuous_U, fun _ _ => integrable_U,
    fun _ _ => le_rfl, ⟨0, fun _ _ => by simp⟩⟩

/-- Vorticity of `U` at `(s, 0, 0)`: its third component is `-(aa2 s - 2 aa s)`. -/
lemma curl_U_two (s : ℝ) :
    vorticity U (EuclideanSpace.single 0 s) 2 = -(aa2 s - 2 * aa s) := by
  simp only [vorticity, curl, directionalCoord]
  rw [U1, U0, d0c1, d1c0]
  simp [bb_zero, bb2_zero]
  ring

lemma vorticity_U_unbounded : ¬ BddAbove (Set.range fun x => ‖vorticity U x‖) := by
  rintro ⟨M, hM⟩
  obtain ⟨s, hs⟩ := aa2_unbounded M
  have h1 : ‖vorticity U (EuclideanSpace.single 0 s)‖ ≤ M := hM ⟨_, rfl⟩
  have h2 : ‖vorticity U (EuclideanSpace.single 0 s) 2‖ ≤ ‖vorticity U (EuclideanSpace.single 0 s)‖ :=
    PiLp.norm_apply_le _ 2
  rw [curl_U_two, Real.norm_eq_abs, abs_neg] at h2
  linarith

/-- **Refutation.** For every `ν > 0`, `FrohmanianTetherRate U ν` is false: the steady path
`u ≡ U`, `p ≡ 0` satisfies `NS_PDE` and `IsPhysicalNSSolution`, but its vorticity is unbounded. -/
theorem not_frohmanianTetherRate_U (ν : ℝ) (hν : 0 < ν) : ¬ FrohmanianTetherRate U ν := by
  intro h
  obtain ⟨_, _, _, _, _, _, _, hb⟩ := h (fun _ => U) (fun _ => fun _ => 0) hν (ns_U ν) rfl phys_U
  exact vorticity_U_unbounded (hb 0 le_rfl)

theorem not_forall_frohmanianTetherRate :
    ¬ ∀ (u₀ : VelocityField) (ν : ℝ), FrohmanianTetherRate u₀ ν :=
  fun h => not_frohmanianTetherRate_U 1 one_pos (h U 1)

/-- Same datum refutes `FrohmanianTetherBound` for every `ν` (no sign condition there). -/
theorem not_frohmanianTetherBound_U (ν : ℝ) : ¬ FrohmanianTetherBound U ν := by
  intro h
  obtain ⟨_, _, _, hb⟩ := h (fun _ => U) (fun _ => fun _ => 0) (ns_U ν) rfl phys_U
  exact vorticity_U_unbounded (hb 0 le_rfl)

end TetherRateCounterexample

#print axioms TetherRateCounterexample.not_frohmanianTetherRate_U
#print axioms TetherRateCounterexample.not_forall_frohmanianTetherRate
#print axioms TetherRateCounterexample.not_frohmanianTetherBound_U
#print axioms TakagiScratch.not_differentiableAt_takagi
