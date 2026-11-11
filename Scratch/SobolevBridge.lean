import Scratch.SobolevEmbedding
import Scratch.R3BKMContinuation

/-! # `H³ ↪ L^∞` on ℝ³ in the repo's Sobolev energy (`R3BKM.sobolevEnergy`, :32)

`|f x j| ≤ 8 ‖f‖_{H³}` for every smooth `f : ℝ³ → ℝ³`, component `j`, point `x`
(no decay assumed). -/

open MeasureTheory Set SobolevR3
open scoped ContDiff ENNReal

noncomputable section
namespace SobolevBridge

/-- One more directional derivative of an iterated derivative. -/
lemma D_iteratedFDeriv {h : E3 → ℝ} (hh : ContDiff ℝ ∞ h) (k : ℕ) (m : Fin k → E3) (i : Fin 3)
    (y : E3) :
    D i (fun z => iteratedFDeriv ℝ k h z m) y = iteratedFDeriv ℝ (k + 1) h y (Fin.cons (e i) m) := by
  rw [iteratedFDeriv_succ_apply_left]
  simp only [D, Fin.cons_zero, Fin.tail_cons]
  exact fderiv_continuousMultilinear_apply_const_apply
    ((hh.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)) y) m (e i)

lemma h_eq_iter0 (h : E3 → ℝ) : h = fun z => iteratedFDeriv ℝ 0 h z Fin.elim0 := by
  funext z; simp

/-- Unit-vector tuple of a word `α`. -/
abbrev U {k : ℕ} (α : Fin k → Fin 3) : Fin k → E3 := fun j => EuclideanSpace.single (α j) (1 : ℝ)

lemma D_word0 {h : E3 → ℝ} (hh : ContDiff ℝ ∞ h) (a : Fin 3) :
    D a h = fun y => iteratedFDeriv ℝ 1 h y (U ![a]) := by
  funext y
  conv_lhs => rw [h_eq_iter0 h]
  rw [D_iteratedFDeriv hh]
  congr 1; funext j; fin_cases j; rfl

lemma D_word1 {h : E3 → ℝ} (hh : ContDiff ℝ ∞ h) (a b : Fin 3) :
    D b (D a h) = fun y => iteratedFDeriv ℝ 2 h y (U ![b, a]) := by
  funext y
  rw [D_word0 hh, D_iteratedFDeriv hh]
  congr 1; funext j; fin_cases j <;> rfl

lemma D_word2 {h : E3 → ℝ} (hh : ContDiff ℝ ∞ h) (a b c : Fin 3) :
    D c (D b (D a h)) = fun y => iteratedFDeriv ℝ 3 h y (U ![c, b, a]) := by
  funext y
  rw [D_word1 hh, D_iteratedFDeriv hh]
  congr 1; funext j; fin_cases j <;> rfl

/-- Component of an iterated derivative. -/
lemma iteratedFDeriv_component {f : E3 → E3} (hf : ContDiff ℝ ∞ f) (j : Fin 3) (k : ℕ)
    (y : E3) (m : Fin k → E3) :
    iteratedFDeriv ℝ k (fun z => f z j) y m = iteratedFDeriv ℝ k f y m j := by
  have := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j).iteratedFDeriv_comp_left
    (hf.contDiffAt (x := y)) (i := k) (by exact_mod_cast le_top)
  have h2 : (fun z => f z j) = (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j) ∘ f := rfl
  rw [h2, this]
  rfl

/-- A single `(k, α)` term is bounded by the full `H³` energy. -/
lemma term_le_energy (f : E3 → E3) {k : ℕ} (hk : k ≤ 3) (α : Fin k → Fin 3) :
    ∫⁻ x, ‖iteratedFDeriv ℝ k f x (U α)‖ₑ ^ 2 ≤ R3BKM.sobolevEnergy 3 f := by
  unfold R3BKM.sobolevEnergy
  have h1 : ∫⁻ x, ‖iteratedFDeriv ℝ k f x (U α)‖ₑ ^ 2 ≤
      ∑ β : Fin k → Fin 3, ∫⁻ x, ‖iteratedFDeriv ℝ k f x (U β)‖ₑ ^ 2 :=
    Finset.single_le_sum (f := fun β : Fin k → Fin 3 =>
      ∫⁻ x, ‖iteratedFDeriv ℝ k f x (U β)‖ₑ ^ 2) (fun _ _ => zero_le _) (Finset.mem_univ α)
  refine h1.trans ?_
  exact Finset.single_le_sum (f := fun k : ℕ => ∑ β : Fin k → Fin 3,
      ∫⁻ x, ‖iteratedFDeriv ℝ k f x (U β)‖ₑ ^ 2) (fun _ _ => zero_le _)
    (Finset.mem_range.2 (by omega))

lemma comp_term_le {f : E3 → E3} (hf : ContDiff ℝ ∞ f) (j : Fin 3) {k : ℕ} (hk : k ≤ 3)
    (α : Fin k → Fin 3) :
    (∫⁻ y, ‖iteratedFDeriv ℝ k (fun z => f z j) y (U α)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
      R3BKM.sobolevEnergy 3 f ^ (1 / 2 : ℝ) := by
  gcongr
  refine le_trans (lintegral_mono fun y => ?_) (term_le_energy f hk α)
  rw [iteratedFDeriv_component hf, ENNReal.rpow_two]
  gcongr
  exact PiLp.enorm_apply_le _ _

/-- **`H³ ↪ L^∞` on ℝ³**: `|f x j| ≤ 8 ‖f‖_{H³}` (no decay assumed). -/
theorem abs_component_le_sobolevEnergy {f : E3 → E3} (hf : ContDiff ℝ ∞ f) (j : Fin 3)
    (x : E3) :
    ENNReal.ofReal |f x j| ≤ 8 * R3BKM.sobolevEnergy 3 f ^ (1 / 2 : ℝ) := by
  set h : E3 → ℝ := fun z => f z j
  have hh : ContDiff ℝ ∞ h := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j).contDiff.comp hf
  have H := abs_le_sum_L2 hh x
  set S := R3BKM.sobolevEnergy 3 f ^ (1 / 2 : ℝ)
  have t0 : (∫⁻ y, ‖h y‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤ S := by
    have := comp_term_le hf j (k := 0) (by norm_num) Fin.elim0
    simpa [h, S] using this
  have t1 : ∀ a, (∫⁻ y, ‖D a h y‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤ S := fun a => by
    rw [D_word0 hh]; exact comp_term_le hf j (by norm_num) _
  have t2 : ∀ a b, (∫⁻ y, ‖D b (D a h) y‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤ S := fun a b => by
    rw [D_word1 hh]; exact comp_term_le hf j (by norm_num) _
  have t3 : ∀ a b c, (∫⁻ y, ‖D c (D b (D a h)) y‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤ S :=
    fun a b c => by rw [D_word2 hh]; exact comp_term_le hf j (by norm_num) _
  refine H.trans ?_
  calc _ ≤ S + S + (S + S) + (S + S + (S + S)) :=
        add_le_add (add_le_add (add_le_add t0 (t1 2)) (add_le_add (t1 1) (t2 1 2)))
          (add_le_add (add_le_add (t1 0) (t2 0 2)) (add_le_add (t2 0 1) (t3 0 1 2)))
    _ = 8 * S := by ring

end SobolevBridge

#print axioms SobolevBridge.abs_component_le_sobolevEnergy
